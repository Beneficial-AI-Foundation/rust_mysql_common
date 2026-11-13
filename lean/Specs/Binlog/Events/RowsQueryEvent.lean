import Proofs.Binlog.Events.RowsQueryEvent.RowsQueryEvent

/-!
# `src/binlog/events/rows_query_event.rs`
    `RowsQueryEvent` (`ROWS_QUERY_LOG_EVENT`, code 29): a length byte (ignored: queries may be
    longer than 255 bytes) and the query (the rest). Covered: `new`, `query_raw`, `into_owned`,
    `SIZE`, `deserialize` (exact on any input), `serialize`, the round trip, `EVENT_TYPE`, `len`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`rowsQueryEnc`, `ReadsAs`).
    **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `query` (lossy UTF-8, excluded); the derived impls.

    **Behaviour to note.** The crate writes `0` as the length byte (MySQL writes the length, mod 256).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RowsQueryEvent and its impls` -/

/-- `new(query)`: that query. -/
recall binlog.events.rows_query_event.RowsQueryEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (q : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into q = ok c) :
    binlog.events.rows_query_event.RowsQueryEvent.new into q ⦃ e => cowList e.query.1 = cowList c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.new_spec
/-- `query_raw`: the query. -/
recall binlog.events.rows_query_event.RowsQueryEvent.query_raw_spec (e : binlog.events.rows_query_event.RowsQueryEvent) :
    binlog.events.rows_query_event.RowsQueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.query_raw_spec
/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.rows_query_event.RowsQueryEvent.into_owned_spec (e : binlog.events.rows_query_event.RowsQueryEvent) :
    binlog.events.rows_query_event.RowsQueryEvent.into_owned e ⦃ e' => (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) e' = (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.into_owned_spec
/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq
/-- `MyDeserialize`: total; an error on empty data, else the query is everything after the first byte. -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) (if 1 ≤ buf.length then some (buf.val.drop 1, []) else none) r rest ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec
/-- `MySerialize`: appends the layout `rowsQueryEnc`. -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rows_query_event.RowsQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (rowsQueryEnc e).length ≤ Usize.max) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsQueryEnc e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip. -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rows_query_event.RowsQueryEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = rowsQueryEnc e) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) = some (cowList e.query.1) ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip
/-- `BinlogEvent::EVENT_TYPE`: `ROWS_QUERY_EVENT` (29). -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ROWS_QUERY_EVENT

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq
/-- `BinlogStruct::len`: the length of what `serialize` writes (`rowsQueryEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rows_query_event.RowsQueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (rowsQueryEnc e).length evLenCap ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec
end mysql_common
