import Defs
import Proofs.Util.StmtBulkSsA
import Proofs.Util.Shared

/-! Statements for `struct SystemVariable and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Helper lemmas: `Proofs/Util/StmtBulkSsA.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `SystemVariable::new(name, value)`: wraps `name.into()` and `value.into()`. -/
theorem packets.session_state_change.SystemVariable.new_spec {X Y : Type}
    (into1 : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (into2 : core.convert.Into Y (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (n : X) (v : Y) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into n = ok c1) (h2 : into2.into v = ok c2) :
    packets.session_state_change.SystemVariable.new into1 into2 n v ⦃ x => x.«name».1 = c1 ∧ x.value.1 = c2 ⦄ := by
  unfold packets.session_state_change.SystemVariable.new
  apply WP.spec_bind (SBSsA.lenenc_new into1 n c1 h1)
  intro x hx
  apply WP.spec_bind (SBSsA.lenenc_new into2 v c2 h2)
  intro y hy
  exact (WP.spec_ok _).mpr ⟨hx, hy⟩

/-- `name_bytes`: the raw name. -/
theorem packets.session_state_change.SystemVariable.name_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_bytes self ⦃ s => s.val = cowList self.«name».1 ⦄ := by
  exact PCSUtil.lenenc_as_bytes self.«name»

/-- `name_str`: the name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.SystemVariable.name_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_str self ⦃ c => LossyUtf8Valid (cowList self.«name».1) c ⦄ := by
  exact Shared.lenenc_as_str self.«name»

/-- `value_bytes`: the raw value. -/
theorem packets.session_state_change.SystemVariable.value_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_bytes self ⦃ s => s.val = cowList self.value.1 ⦄ := by
  exact PCSUtil.lenenc_as_bytes self.value

/-- `value_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.SystemVariable.value_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_str self ⦃ c => LossyUtf8Valid (cowList self.value.1) c ⦄ := by
  exact Shared.lenenc_as_str self.value

/-- `into_owned`: the same name and value. -/
theorem packets.session_state_change.SystemVariable.into_owned_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.into_owned self ⦃ x =>
      cowList x.«name».1 = cowList self.«name».1 ∧ cowList x.value.1 = cowList self.value.1 ⦄ := by
  unfold packets.session_state_change.SystemVariable.into_owned
  apply WP.spec_bind (PCSUtil.raw_into_owned _ self.«name»)
  intro x hx
  apply WP.spec_bind (PCSUtil.raw_into_owned _ self.value)
  intro y hy
  exact (WP.spec_ok _).mpr ⟨hx, hy⟩

/-- `MyDeserialize for SystemVariable`: `SIZE` is `None`. -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for SystemVariable`: total; `sysVarRead` (the name, then the value, as
    length-encoded strings). -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => (cowList x.«name».1, cowList x.value.1)), rest.val) = sysVarRead buf.val ⦄ := by
  unfold packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with SBSsA.lenenc_parse_unchecked h64 buf as ⟨ r, buf1, hr ⟩
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_tc_ok]
    simp_all [sysVarRead, okPart]
  | Ok rb =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    step with SBSsA.lenenc_parse_unchecked h64 buf1 as ⟨ r1, buf2, hr1 ⟩
    cases r1 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_tc_ok]
      simp_all [sysVarRead, okPart]
    | Ok rb1 =>
      simp_all [sysVarRead, okPart]

/-- `MySerialize for SystemVariable`: appends the name, then the value, as length-encoded
    strings. -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SystemVariable) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1)).length ≤ Usize.max) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1) ⦄ := by
  unfold packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize
  step with PCSUtil.lenenc_raw_serialize self.«name» buf (by simp at h ⊢; omega) as ⟨ buf1, hbuf1 ⟩
  step with PCSUtil.lenenc_raw_serialize self.value buf1 (by simp_all; omega) as ⟨ buf2, hbuf2 ⟩
  simp_all

end mysql_common
