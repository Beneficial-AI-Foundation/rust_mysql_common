import Defs

/-! Statements for `struct IntvarEvent and its impls` (spec file: `Specs/Binlog/Events/IntvarEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(subtype, value)`: those fields. -/
theorem binlog.events.intvar_event.IntvarEvent.new_spec (t : binlog.consts.IntvarEventType) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.new t value ⦃ e => e.subtype.1 = t ∧ e.value.1 = value ⦄ := by
  sorry

/-- `subtype`: the subtype. -/
theorem binlog.events.intvar_event.IntvarEvent.impl.subtype_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.subtype e = ok e.subtype.1 := by
  sorry

/-- `value`: the value. -/
theorem binlog.events.intvar_event.IntvarEvent.impl.value_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.value e = ok e.value.1 := by
  sorry

/-- `with_subtype`: replaces the subtype. -/
theorem binlog.events.intvar_event.IntvarEvent.with_subtype_spec (e : binlog.events.intvar_event.IntvarEvent) (t : binlog.consts.IntvarEventType) :
    binlog.events.intvar_event.IntvarEvent.with_subtype e t ⦃ e' => e'.subtype.1 = t ∧ e'.value = e.value ⦄ := by
  sorry

/-- `with_value`: replaces the value. -/
theorem binlog.events.intvar_event.IntvarEvent.with_value_spec (e : binlog.events.intvar_event.IntvarEvent) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.with_value e value ⦃ e' => e'.subtype = e.subtype ∧ e'.value.1 = value ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `some 9#usize`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 9#usize := by
  sorry

/-- `MyDeserialize` on at least 9 bytes: `intvarRead` (an unknown subtype is an error). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 9 ≤ buf.length) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄ := by
  sorry

/-- `MyDeserialize` panics on fewer than 9 bytes, unless the first byte is an unknown subtype (then it is an error). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 9)
    (hs : ∀ b, buf.val.head? = some b → intvarTypeOfCode b.val ≠ none) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic := by
  sorry

/-- `buf.parse::<IntvarEvent>(ctx)`: total (`SIZE` checked first); `intvarRead`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `intvarEnc`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.intvar_event.IntvarEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (intvarEnc e).length ≤ Usize.max) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ intvarEnc e ⦄ := by
  sorry

/-- Round trip. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.intvar_event.IntvarEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = intvarEnc e ++ tail) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `INTVAR_EVENT` (5). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INTVAR_EVENT := by
  sorry

/-- `BinlogStruct::len`: 9 (= the length of `intvarEnc`). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.intvar_event.IntvarEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 9#usize := by
  sorry

end mysql_common
