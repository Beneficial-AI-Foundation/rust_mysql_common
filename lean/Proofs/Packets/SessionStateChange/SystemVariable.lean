import Defs

/-! Statements for `struct SystemVariable and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Proofs: TODO. -/

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
  sorry

/-- `name_bytes`: the raw name. -/
theorem packets.session_state_change.SystemVariable.name_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_bytes self ⦃ s => s.val = cowList self.«name».1 ⦄ := by
  sorry

/-- `name_str`: the name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.SystemVariable.name_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_str self ⦃ c => LossyUtf8Valid (cowList self.«name».1) c ⦄ := by
  sorry

/-- `value_bytes`: the raw value. -/
theorem packets.session_state_change.SystemVariable.value_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_bytes self ⦃ s => s.val = cowList self.value.1 ⦄ := by
  sorry

/-- `value_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.SystemVariable.value_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_str self ⦃ c => LossyUtf8Valid (cowList self.value.1) c ⦄ := by
  sorry

/-- `into_owned`: the same name and value. -/
theorem packets.session_state_change.SystemVariable.into_owned_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.into_owned self ⦃ x =>
      cowList x.«name».1 = cowList self.«name».1 ∧ cowList x.value.1 = cowList self.value.1 ⦄ := by
  sorry

/-- `MyDeserialize for SystemVariable`: `SIZE` is `None`. -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for SystemVariable`: total; `sysVarRead` (the name, then the value, as
    length-encoded strings). -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => (cowList x.«name».1, cowList x.value.1)), rest.val) = sysVarRead buf.val ⦄ := by
  sorry

/-- `MySerialize for SystemVariable`: appends the name, then the value, as length-encoded
    strings. -/
theorem packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SystemVariable) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1)).length ≤ Usize.max) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1) ⦄ := by
  sorry

end mysql_common
