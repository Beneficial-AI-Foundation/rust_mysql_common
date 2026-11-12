import Defs

/-! Statements for `struct CapabilityFlags and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`capabilityFlagsAll`). -/
theorem constants.CapabilityFlags.all_spec :
    constants.CapabilityFlags.all ⦃ r => r.val = capabilityFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem constants.CapabilityFlags.from_bits_truncate_spec (bits : U32) :
    constants.CapabilityFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& capabilityFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem constants.CapabilityFlags.from_bits_spec (bits : U32) :
    constants.CapabilityFlags.from_bits bits ⦃ r => r = if bits.val &&& capabilityFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from_spec (val : U32) :
    constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from val ⦃ r =>
      r = if val.val &&& capabilityFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem constants.CapabilityFlags.bits_eq (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.CapabilityFlags.from_bits_retain_eq (bits : U32) :
    constants.CapabilityFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem constants.CapabilityFlags.empty_spec :
    constants.CapabilityFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem constants.CapabilityFlags.is_empty_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem constants.CapabilityFlags.is_all_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_all self ⦃ b => (b ↔ capabilityFlagsAll &&& self.val = capabilityFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem constants.CapabilityFlags.intersects_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem constants.CapabilityFlags.contains_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem constants.CapabilityFlags.union_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem constants.CapabilityFlags.insert_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem constants.CapabilityFlags.intersection_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem constants.CapabilityFlags.difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.difference self other ⦃ r => r.val = andNot 32 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem constants.CapabilityFlags.remove_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.remove self other ⦃ r => r.val = andNot 32 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem constants.CapabilityFlags.symmetric_difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem constants.CapabilityFlags.toggle_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem constants.CapabilityFlags.set_spec (self other : constants.CapabilityFlags) (value : Bool) :
    constants.CapabilityFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 32 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem constants.CapabilityFlags.complement_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.complement self ⦃ r => r.val = complementBits 32 self.val &&& capabilityFlagsAll ⦄ := by
  sorry

end mysql_common
