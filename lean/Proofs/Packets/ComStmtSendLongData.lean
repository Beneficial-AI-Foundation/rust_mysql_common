import Defs

/-! Statements for `struct ComStmtSendLongData and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComStmtSendLongData::new(stmt_id, param_index, data)`: the given fields (`data.into()`). -/
theorem packets.ComStmtSendLongData.new_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (stmt_id : U32) (param_index : U16) (data : T)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into data = ok c) :
    packets.ComStmtSendLongData.new into stmt_id param_index data ⦃ p =>
      p.stmt_id.1 = stmt_id ∧ p.param_index.1 = param_index ∧ p.data.1 = c ⦄ := by
  sorry

/-- `into_owned`: the same fields. -/
theorem packets.ComStmtSendLongData.into_owned_spec (self : packets.ComStmtSendLongData) :
    packets.ComStmtSendLongData.into_owned self ⦃ p =>
      p.stmt_id.1 = self.stmt_id.1 ∧ p.param_index.1 = self.param_index.1 ∧
      cowList p.data.1 = cowList self.data.1 ⦄ := by
  sorry

/-- `MySerialize for ComStmtSendLongData`: appends the protocol's packet `sendLongDataEnc`
    (`0x18`, statement id, parameter index, all the data). -/
theorem packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtSendLongData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 + (cowList self.data.1).length ≤ Usize.max) :
    packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++
        sendLongDataEnc self.stmt_id.1.val self.param_index.1.val (cowList self.data.1) ⦄ := by
  sorry

end mysql_common
