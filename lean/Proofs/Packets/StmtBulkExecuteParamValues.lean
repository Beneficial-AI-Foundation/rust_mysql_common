import Defs

/-! Statements for `struct StmtBulkExecuteParamValues and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `AsRef<[StmtBulkExecuteParamValue]>`: the values. -/
theorem packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref_spec
    (self : packets.StmtBulkExecuteParamValues) :
    packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref self ⦃ s =>
      s.val = self.values.val ⦄ := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamValues`: `SIZE` is `None`. -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for StmtBulkExecuteParamValues` with the parameters `params`: one value per
    parameter (`bulkValuesRead`), exactly, whenever that reader returns. -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (r0 : Option (List (Nat × Val))) (rest0 : List U8)
    (h : bulkValuesRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map (fun vs => vs.values.val.map bulkIV) = r0 ∧ rest.val = rest0 ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValues` panics where `bulkValuesRead`
    does: a non-`NULL` indicator for a parameter whose column type the binary reader does not
    support (`TIMESTAMP2`, `DATETIME2`, `TIME2`, `TYPED_ARRAY`, `UNKNOWN`). -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (e : Error) (h : bulkValuesRead (bulkParams params) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e := by
  sorry

/-- `MySerialize for StmtBulkExecuteParamValues`: appends each value (`bulkValueEnc`). -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValues) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((self.values.val.map bulkIV).flatMap bulkValueEnc).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (self.values.val.map bulkIV).flatMap bulkValueEnc ⦄ := by
  sorry

end mysql_common
