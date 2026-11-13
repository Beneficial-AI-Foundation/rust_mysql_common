import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt

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
  unfold packets.ComStmtSendLongData.new
  rw [misc.raw.int.ConstU8.new_eq, misc.raw.int.RawInt.new_eq, misc.raw.int.RawInt.new_eq,
    misc.raw.bytes.RawBytes.new_eq _ into data c h]
  exact WP.spec_bind ((WP.spec_ok (p := fun _ => True) ()).mpr trivial) fun _ _ =>
    WP.spec_bind ((WP.spec_ok (p := fun x => x = (stmt_id, ())) _).mpr rfl) fun _ h1 =>
    WP.spec_bind ((WP.spec_ok (p := fun x => x = (param_index, ())) _).mpr rfl) fun _ h2 =>
    WP.spec_bind ((WP.spec_ok (p := fun x => x = (c, ())) _).mpr rfl) fun _ h3 =>
    (WP.spec_ok _).mpr (by subst h1 h2 h3; exact ⟨rfl, rfl, rfl⟩)

/-- `into_owned`: the same fields. -/
theorem packets.ComStmtSendLongData.into_owned_spec (self : packets.ComStmtSendLongData) :
    packets.ComStmtSendLongData.into_owned self ⦃ p =>
      p.stmt_id.1 = self.stmt_id.1 ∧ p.param_index.1 = self.param_index.1 ∧
      cowList p.data.1 = cowList self.data.1 ⦄ := by
  unfold packets.ComStmtSendLongData.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb, hrb ⟩
  simp [hrb]

/-- `MySerialize for ComStmtSendLongData`: appends the protocol's packet `sendLongDataEnc`
    (`0x18`, statement id, parameter index, all the data). -/
theorem packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtSendLongData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 + (cowList self.data.1).length ≤ Usize.max) :
    packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++
        sendLongDataEnc self.stmt_id.1.val self.param_index.1.val (cowList self.data.1) ⦄ := by
  unfold packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨ b1, h1 ⟩
  step with PCSUtil.rawint_u32_serialize as ⟨ b2, h2 ⟩
  · simp only [PKUtil.vec_len, h1] at *; simp; omega
  step with PCSUtil.rawint_u16_serialize as ⟨ b3, h3 ⟩
  · simp only [PKUtil.vec_len, h1, h2] at *; simp; omega
  step with PKUtil.eof_ser as ⟨ b, hb ⟩
  · simp only [PKUtil.vec_len, h1, h2, h3] at *; simp; omega
  simp [hb, h3, h2, h1, sendLongDataEnc]; rfl

end mysql_common
