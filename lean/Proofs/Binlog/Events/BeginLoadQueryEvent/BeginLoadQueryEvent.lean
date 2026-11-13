import Defs

/-! Statements for `struct BeginLoadQueryEvent and its impls` (spec file: `Specs/Binlog/Events/BeginLoadQueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(file_id)`: that id and an empty block. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.new_spec (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.new fid ⦃ e => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e = (fid.val, []) ⦄ := by
  sorry

/-- `with_file_id`: replaces the id. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id e fid ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fid.val, cowList e.block_data.1) ⦄ := by
  sorry

/-- `with_block_data`: replaces the block. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (b : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into b = ok c) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data into e b ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (e.file_id.1.val, cowList c) ⦄ := by
  sorry

/-- `file_id`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id_eq (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id e = ok e.file_id.1 := by
  sorry

/-- `block_data`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data e ⦃ s => s.val = cowList e.block_data.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned e ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; 4 bytes of id, the block as the rest. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) (if 4 ≤ buf.length then some ((leNat (buf.val.take 4), buf.val.drop 4), []) else none) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `beginLoadQueryEnc`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (beginLoadQueryEnc e).length ≤ Usize.max) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ beginLoadQueryEnc e ⦄ := by
  sorry

/-- Round trip. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = beginLoadQueryEnc e) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) = some ((fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e) ∧ rest.val = [] ⦄ := by
  sorry

/-- `BinlogStruct::len`: the length of what `serialize` writes (`beginLoadQueryEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (beginLoadQueryEnc e).length evLenCap ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `BEGIN_LOAD_QUERY_EVENT` (17). -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .BEGIN_LOAD_QUERY_EVENT := by
  sorry

end mysql_common
