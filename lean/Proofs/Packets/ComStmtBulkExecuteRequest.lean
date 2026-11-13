import Defs

/-! Statements for `struct ComStmtBulkExecuteRequest and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComStmtBulkExecuteRequest::new(stmt_id, bulk_flags, rows)`: exactly `bulkNewOut` (`NoParams`
    for no rows, `MixedArity` if the rows differ in length, else the statement id, the flags,
    the merged types `bulkTypes` if the flags have `SEND_TYPES_TO_SERVER`, and every value with
    its indicator). Precondition: the number of values fits in a `usize`. -/
theorem packets.ComStmtBulkExecuteRequest.new_spec (stmt_id : U32)
    (bulk_flags : constants.StmtBulkExecuteFlags) (values : alloc.vec.Vec (alloc.vec.Vec value.Value))
    (hv : (values.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.new stmt_id bulk_flags values ⦃ r =>
      (bulkNewOut stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue))).Matches r ⦄ := by
  sorry

/-- `stmt_id`: the statement id. -/
theorem packets.ComStmtBulkExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.stmt_id self = ok self.stmt_id.1 := by
  sorry

/-- `bulk_flags`: the flags. -/
theorem packets.ComStmtBulkExecuteRequest.impl.bulk_flags_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.bulk_flags self = ok self.bulk_flags.1 := by
  sorry

/-- `types`: the parameter types. -/
theorem packets.ComStmtBulkExecuteRequest.impl.types_spec (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.types self ⦃ s => s.val = cowList self.types.1 ⦄ := by
  sorry

/-- `values`: the values. -/
theorem packets.ComStmtBulkExecuteRequest.impl.values_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.values self = ok self.values := by
  sorry

/-- `MyDeserialize for ComStmtBulkExecuteRequest`: `SIZE` is `None`. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for ComStmtBulkExecuteRequest` with the parameters `params` the caller knows:
    exactly `bulkReqRead` whenever that reader returns. **Crate bugs** (see `bulkReqRead`):
    with `SEND_TYPES_TO_SERVER` each type is read from 3 bytes although it is sent in 2, so a
    request with parameters and types is misread (`Defs.bulkReqRead_types_misread`); only the
    first row of values is read (`Defs.bulkReqRead_first_row_only`). Precondition: `3 *
    params.len()` does not overflow `usize` (true of every real `Vec`). -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (r0 : Option BulkReq) (rest0 : List U8)
    (h : bulkReqRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map BulkReq.of = r0 ∧ rest.val = rest0 ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for ComStmtBulkExecuteRequest` panics where `bulkReqRead` does:
    a value for a parameter whose column type (sent by the client with `SEND_TYPES_TO_SERVER`,
    or known to the caller) the binary reader does not support. A client can thus crash a
    server-side reader. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (e : Error)
    (h : bulkReqRead (bulkParams params) buf.val = .panic e) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e := by
  sorry

/-- `MySerialize for ComStmtBulkExecuteRequest`: appends `bulkReqEnc` (header, statement id,
    flags, the types only with `SEND_TYPES_TO_SERVER`, the values). For a request made by `new`
    this is the protocol's packet. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtBulkExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkReqEnc (BulkReq.of self)).length ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkReqEnc (BulkReq.of self) ⦄ := by
  sorry

end mysql_common
