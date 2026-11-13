import Defs

/-! Statements for `struct StmtBulkExecuteParamValue and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `StmtBulkExecuteParamValue::new(v)`: the value, with the indicator `NULL` for `NULL` and
    `NONE` otherwise (`bulkInd`). -/
theorem packets.StmtBulkExecuteParamValue.new_spec (v : value.Value) :
    packets.StmtBulkExecuteParamValue.new v ⦃ x =>
      x.value = v ∧ bulkIndicatorCode x.indicator.1 = bulkInd (Val.ofValue v) ⦄ := by
  sorry

/-- `indicator`: the indicator. -/
theorem packets.StmtBulkExecuteParamValue.impl.indicator_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.indicator self = ok self.indicator.1 := by
  sorry

/-- `value`: the value. -/
theorem packets.StmtBulkExecuteParamValue.impl.value_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.value self = ok self.value := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamValue`: `SIZE` is `None`. -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamValue` for a parameter of column type `ct` with
    column flags `flags`: exactly `bulkValueRead` whenever that reader returns. **Crate
    behaviour**: a value is read after the `DEFAULT` and `IGNORE` indicators (the protocol sends
    none). -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf)
    (r0 : Option (Nat × Val)) (rest0 : List U8)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      (okPart r).map bulkIV = r0 ∧ rest.val = rest0 ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValue` panics where `bulkValueRead`
    does: an indicator other than `NULL` for a column type the binary reader does not support. -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf) (e : Error)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf = fail e := by
  sorry

/-- `MySerialize for StmtBulkExecuteParamValue`: appends `bulkValueEnc` (the indicator, then the
    binary encoding of the value). -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValue) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkValueEnc (bulkIV self)).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkValueEnc (bulkIV self) ⦄ := by
  sorry

end mysql_common
