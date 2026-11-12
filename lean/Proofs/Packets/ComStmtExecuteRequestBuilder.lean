import Defs

/-! Statements for `struct ComStmtExecuteRequestBuilder and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the builder for the statement. -/
theorem packets.ComStmtExecuteRequestBuilder.new_eq (stmt_id : U32) :
    packets.ComStmtExecuteRequestBuilder.new stmt_id = ok { stmt_id } := by
  sorry

/-- `build(params)`: the request for the statement with no cursor, iteration count 1, the NULL bitmap of the parameters (offset 0; a parameter is NULL iff its binary encoding is empty), new-params-bound flag 1 and the parameters; `as_long_data` (also returned) iff the length the builder computes exceeds `MAX_PAYLOAD_LEN`. (The bound keeps that computation from overflowing.) -/
theorem packets.ComStmtExecuteRequestBuilder.build_spec (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value)
    (h : stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    packets.ComStmtExecuteRequestBuilder.build self params ⦃ req b =>
      req.stmt_id.1 = self.stmt_id ∧ req.flags.1.val = 0 ∧
      cowList req.bitmap.1 = nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v))) ∧
      req.params_flags.1.val = 1 ∧ req.params = params ∧ req.as_long_data = b ∧
      (b = true ↔ maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue)) ⦄ := by
  sorry

/-- Headline: `build` then `serialize` appends the protocol's `COM_STMT_EXECUTE` packet (`comStmtExecute`), with the `Bytes` values left out iff `as_long_data`, for at most 65536 parameters (beyond, the bitmap is truncated). -/
theorem packets.ComStmtExecuteRequestBuilder.build_serialize (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value) (buf : alloc.vec.Vec U8)
    (hn : params.length ≤ 65536) (h : buf.length + stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    (packets.ComStmtExecuteRequestBuilder.build self params >>= fun p =>
      packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize p.1 buf) ⦃ buf' =>
      buf'.val = buf.val ++ comStmtExecute self.stmt_id.val (params.val.map Val.ofValue)
        (decide (maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue))) ⦄ := by
  sorry

end mysql_common
