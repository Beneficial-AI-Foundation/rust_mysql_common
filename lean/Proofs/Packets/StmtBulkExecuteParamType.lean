import Defs

/-! Statements for `struct StmtBulkExecuteParamType and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `StmtBulkExecuteParamType::new(type, flags)`: the given type and flags. -/
theorem packets.StmtBulkExecuteParamType.new_eq (type : constants.ColumnType)
    (flags : constants.StmtExecuteParamFlags) :
    packets.StmtBulkExecuteParamType.new type flags = ok ⟨(type, ()), (flags, ())⟩ := by
  sorry

/-- `from_value(v)`: the type the crate sends for the value (`bulkTy`). -/
theorem packets.StmtBulkExecuteParamType.from_value_spec (v : value.Value) :
    packets.StmtBulkExecuteParamType.from_value v ⦃ t =>
      (columnTypeCode t.type.1, t.flags.1.val) = bulkTy (Val.ofValue v) ⦄ := by
  sorry

/-- `column_type`: the type. -/
theorem packets.StmtBulkExecuteParamType.column_type_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.column_type self = ok self.type.1 := by
  sorry

/-- `flags`: the flags. -/
theorem packets.StmtBulkExecuteParamType.impl.flags_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.impl.flags self = ok self.flags.1 := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamType`: **`SIZE` is `Some(3)`, but the type is 2
    bytes on the wire** (crate bug): `parse` (`parse_spec`) and the request reader consume 3
    bytes per type. -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 3#usize := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamType`: total; `bulkTypeRead` (a known type code,
    then a flag byte 0 or 128). -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)), rest.val) =
        bulkTypeRead buf.val ⦄ := by
  sorry

/-- `buf.parse::<StmtBulkExecuteParamType>(())`: total; **consumes 3 bytes** (`SIZE`), of which
    `bulkTypeRead` reads two; an error with the buffer unchanged on fewer than 3 bytes (so a
    2-byte type at the end of a packet is rejected). -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec
    (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)) = (bulkTypeRead (buf.val.take 3)).1 ∧
        rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize for StmtBulkExecuteParamType`: appends the 2 bytes `bulkTypeEnc` (type code,
    flag byte). -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamType) (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkTypeEnc (columnTypeCode self.type.1, self.flags.1.val) ⦄ := by
  sorry

end mysql_common
