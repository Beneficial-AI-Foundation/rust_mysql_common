import Defs

/-! Statements for `struct RandEvent and its impls` (spec file: `Specs/Binlog/Events/RandEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize::SIZE` is `some 16#usize`. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 16#usize := by
  sorry

/-- `MyDeserialize` on at least 16 bytes: the two seeds. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) = some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `MyDeserialize` panics on fewer than 16 bytes. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 16) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic := by
  sorry

/-- `buf.parse::<RandEvent>(ctx)`: total; an error on fewer than 16 bytes. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) (if 16 ≤ buf.length then some ((leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)), buf.val.drop 16) else none) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `randEnc`. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rand_event.RandEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (randEnc e).length ≤ Usize.max) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ randEnc e ⦄ := by
  sorry

/-- Round trip. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rand_event.RandEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = randEnc e ++ tail) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `RAND_EVENT` (13). -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .RAND_EVENT := by
  sorry

/-- **Upstream bug:** `BinlogStruct::len` is 8, but the event data is 16 bytes (`randEnc`, two `u64`). -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.rand_event.RandEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 8#usize := by
  sorry

end mysql_common
