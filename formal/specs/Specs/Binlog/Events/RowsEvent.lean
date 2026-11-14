import Proofs.Binlog.Events.RowsEvent.RowsEvent
import Proofs.Binlog.Events.RowsEvent.RowsEventRows

/-!
# `src/binlog/events/rows_event.rs`
    `RowsEvent`, the raw rows event shared by the seven rows-event types (their files wrap it).
    Covered: `event_type`, `table_id`, `num_columns`, `rows_data`, `flags`, `flags_raw`, `len`
    (exact, with the v1 quirk), `rows` (the iterator's fields), `into_owned`, `SIZE`,
    `deserialize` (exact on any input), `serialize`, the round trip; `RowsEventRows::new`.

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155, in
    particular 143, 150, 155: the bitmaps as `RawBytes<BareBitmapBytes>`). The reader statements
    take `Target64` (`div_ceil(8) as usize` of the wire column count).

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. When a reader fails, what it leaves of the buffer is not stated.

    **Definitions used.** `Defs/BinlogEvents.lean` (`RowsView`, `rowsView`, `rowsEnc`, `rowsRead`,
    `RowsConsistent`, `rowsLenCrate`, `rowsIsV2`, `rowsIsUpdate`, `rowsIsDelete`, `eventTypeCode`,
    `rowsEventFlagsAll`, `postHeaderLen`, `fdeLens`, `takeExact`, `optFst`, `evLenCap`, `ReadsAs`),
    `Defs/LenEnc.lean`, `Defs/Bytes.lean` (`Target64`). **Trusted axioms:** none beyond
    `io::Error`'s.

    **Not covered.** `columns_before_image` / `columns_after_image` (`bitvec`) and
    `RowsEventRows`'s `Iterator` (it parses `BinlogRow`s): excluded; the derived impls.

    **Behaviour to note.**
    * **`len` counts the 2-byte extra-data length for every type**, but `serialize` writes it only
      for v2 types: for a v1 event `len` is 2 more than what is written (`len_v1`).
    * The reader decides whether there is extra data by comparing the type's post-header length with
      `WRITE_ROWS_EVENT`'s (both from the FDE) (MySQL compares with the constant
      `ROWS_HEADER_LEN_V2` = 10; equivalent for real FDEs); `serialize` decides by the type. An
      extra-data length below 2 reads as no extra data. A post-header of 6 bytes means a 4-byte
      table id (pre-5.1.4 servers).
    * The bitmaps are read as `(n + 7) / 8` bytes; the rows are kept raw.

    (Of these definitions, `eventTypeCode`, `rowsEventFlagsAll` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RowsEvent and its impls` -/

/-- `event_type`. -/
recall binlog.events.rows_event.RowsEvent.impl.event_type_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.event_type e = ok e.event_type

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.impl.event_type_eq
/-- `table_id`. -/
recall binlog.events.rows_event.RowsEvent.impl.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.table_id e = ok e.table_id.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.impl.table_id_eq
/-- `num_columns`. -/
recall binlog.events.rows_event.RowsEvent.impl.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.num_columns e = ok e.num_columns.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.impl.num_columns_eq
/-- `rows_data`: the raw rows. -/
recall binlog.events.rows_event.RowsEvent.impl.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.impl.rows_data_spec
/-- `flags`: the known flag bits. -/
recall binlog.events.rows_event.RowsEvent.impl.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.impl.flags_spec
/-- `flags_raw`: all the flag bits. -/
recall binlog.events.rows_event.RowsEvent.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.flags_raw e = ok e.flags.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.flags_raw_eq
/-- `len`: `rowsLenCrate`. (64-bit target, as configured). -/
recall binlog.events.rows_event.RowsEvent.len_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = rowsLenCrate e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.len_spec
/-- `len` of a consistent v2 event: the length `serialize` writes, capped. -/
recall binlog.events.rows_event.RowsEvent.len_v2 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h2 : rowsIsV2 e.event_type = true) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = min (rowsEnc e).length evLenCap ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.len_v2
/-- **Quirk:** `len` of a consistent v1 event is 2 more than the length `serialize` writes (when under the cap). -/
recall binlog.events.rows_event.RowsEvent.len_v1 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false) (v : binlog.consts.BinlogVersion)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = (rowsEnc e).length + 2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.len_v1
/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
recall binlog.events.rows_event.RowsEvent.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.rows_event.RowsEvent.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.rows_spec
/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.rows_event.RowsEvent.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.into_owned_spec
/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq
/-- `MyDeserialize` with the context's event type and FDE: total; `rowsRead`. `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
recall binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize_spec (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (ctx : binlog.events.rows_event.RowsEventCtx) (buf : io.ParseBuf) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead ctx.event_type (postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type) (postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄

/-- [propext, Classical.choice, Quot.sound, core.mem.size_of, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize_spec
/-- `MySerialize`: appends `rowsEnc`. (64-bit target, as configured). -/
recall binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip, for a consistent event of the context's type with a table id below `2^48`, read with an FDE whose post-header lengths agree with the type (6 bytes excluded; equal to `WRITE_ROWS_EVENT`'s iff v2). `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
recall binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.roundtrip (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.events.rows_event.RowsEventCtx) (he : eventTypeCode ctx.event_type = eventTypeCode e.event_type)
    (hp : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type ≠ 6) (hv : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type = postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT ↔ rowsIsV2 e.event_type = true)
    (buf : io.ParseBuf) (h : buf.val = rowsEnc e) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => (okPart r).map rowsView = some (rowsView e) ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.mem.size_of, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.roundtrip
/-! ### `struct RowsEventRows and its impls` -/

/-- `new` (crate-private constructor). -/
recall binlog.events.rows_event.RowsEventRows.new_eq (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) (d : io.ParseBuf) :
    binlog.events.rows_event.RowsEventRows.new e tme d = ok { rows_event := e, table_map_event := tme, rows_data := d }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_event.RowsEventRows.new_eq
end mysql_common
