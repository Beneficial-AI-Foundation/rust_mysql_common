import Proofs.Binlog.Events.WriteRowsEventV1.WriteRowsEventV1

/-!
# `src/binlog/events/write_rows_event_v1.rs`
    `WriteRowsEventV1` (`WRITE_ROWS_EVENT_V1`, code 23): a `RowsEvent` of that type. Covered: `table_id`,
    `num_columns`, `rows_data`, `flags`, `flags_raw`, `rows`, `into_owned`, `SIZE`,
    `deserialize` (exact on any input: the rows reader with type 23), `serialize`, `len`,
    `EVENT_TYPE`. The layout statements are those of `Specs/Binlog/Events/RowsEvent.lean`.
    (`WriteRowsEventV1` is a newtype of `RowsEvent`; in Lean a definition equal to it, so the statements
    take the `RowsEvent`.)

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155, in
    particular 143, 150, 155: the bitmaps as `RawBytes<BareBitmapBytes>`). The reader statements
    take `Target64` (`div_ceil(8) as usize` of the wire column count).

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. When a reader fails, what it leaves of the buffer is not stated.

    **Definitions used.** `Defs/BinlogEvents.lean` (`rowsView`, `rowsEnc`, `rowsRead`,
    `rowsLenCrate`, `rowsEventFlagsAll`, `postHeaderLen`, `fdeLens`, `ReadsAs`), `Defs/Bytes.lean`
    (`Target64`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The `bitvec` views (`columns_before_image` / `columns_after_image`,
    excluded; they `expect` the bitmap of a rows event read from the wire); the derived impls.

    (Of these definitions, `rowsEventFlagsAll` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct WriteRowsEventV1 and its impls` -/

/-- `table_id`. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id e = ok e.table_id.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id_eq
/-- `num_columns`. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns e = ok e.num_columns.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns_eq
/-- `rows_data`: the raw rows. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data_spec
/-- `flags`: the known flag bits. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_spec
/-- `flags_raw`: all the flag bits. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_raw e = ok e.flags.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_raw_eq
/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_spec
/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned_spec
/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq
/-- `MyDeserialize`: total; `rowsRead` with type `WRITE_ROWS_EVENT_V1` and the FDE's post-header lengths. `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead .WRITE_ROWS_EVENT_V1 (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT_V1) (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄

/-- [propext, Classical.choice, Quot.sound, core.mem.size_of, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec
/-- `MySerialize`: appends `rowsEnc`. (64-bit target, as configured). -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- `BinlogStruct::len`: `rowsLenCrate` (see `RowsEvent::len`). (64-bit target, as configured). -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = rowsLenCrate e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len_spec
/-- `BinlogEvent::EVENT_TYPE`: `WRITE_ROWS_EVENT_V1` (23). -/
recall binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .WRITE_ROWS_EVENT_V1

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq
end mysql_common
