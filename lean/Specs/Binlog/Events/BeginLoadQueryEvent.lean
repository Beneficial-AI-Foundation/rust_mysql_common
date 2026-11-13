import Proofs.Binlog.Events.BeginLoadQueryEvent.BeginLoadQueryEvent

/-!
# `src/binlog/events/begin_load_query_event.rs`
    `BeginLoadQueryEvent` (`BEGIN_LOAD_QUERY_EVENT`, code 17): `file_id` (4) and a block of the
    loaded file (the rest). Covered: `new`, `with_file_id`, `with_block_data`, `file_id`,
    `block_data`, `into_owned`, `SIZE`, `deserialize` (exact on any input), `serialize`, the round
    trip, `len`, `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`beginLoadQueryEnc`, `ReadsAs`).
    **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The derived impls.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct BeginLoadQueryEvent and its impls` -/

/-- `new(file_id)`: that id and an empty block. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.new_spec (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.new fid ⦃ e => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e = (fid.val, []) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.new_spec`

/-- `with_file_id`: replaces the id. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id e fid ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fid.val, cowList e.block_data.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id_spec`

/-- `with_block_data`: replaces the block. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (b : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into b = ok c) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data into e b ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (e.file_id.1.val, cowList c) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data_spec`

/-- `file_id`. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id_eq (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id e = ok e.file_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id_eq`

/-- `block_data`. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data e ⦃ s => s.val = cowList e.block_data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data_spec`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned e ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; 4 bytes of id, the block as the rest. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) (if 4 ≤ buf.length then some ((leNat (buf.val.take 4), buf.val.drop 4), []) else none) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `beginLoadQueryEnc`. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (beginLoadQueryEnc e).length ≤ Usize.max) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ beginLoadQueryEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = beginLoadQueryEnc e) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) = some ((fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogStruct::len`: the length of what `serialize` writes (`beginLoadQueryEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (beginLoadQueryEnc e).length evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

/-- `BinlogEvent::EVENT_TYPE`: `BEGIN_LOAD_QUERY_EVENT` (17). -/
recall binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .BEGIN_LOAD_QUERY_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

end mysql_common
