import Defs

/-! Statements for `struct StatusFlags and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`statusFlagsAll`). -/
theorem constants.StatusFlags.all_spec :
    constants.StatusFlags.all ⦃ r => r.val = statusFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem constants.StatusFlags.from_bits_truncate_spec (bits : U16) :
    constants.StatusFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& statusFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem constants.StatusFlags.from_bits_spec (bits : U16) :
    constants.StatusFlags.from_bits bits ⦃ r => r = if bits.val &&& statusFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from_spec (val : U16) :
    constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from val ⦃ r =>
      r = if val.val &&& statusFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem constants.StatusFlags.bits_eq (self : constants.StatusFlags) :
    constants.StatusFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.StatusFlags.from_bits_retain_eq (bits : U16) :
    constants.StatusFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem constants.StatusFlags.empty_spec :
    constants.StatusFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem constants.StatusFlags.is_empty_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem constants.StatusFlags.is_all_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_all self ⦃ b => (b ↔ statusFlagsAll &&& self.val = statusFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem constants.StatusFlags.intersects_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem constants.StatusFlags.contains_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem constants.StatusFlags.union_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem constants.StatusFlags.insert_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem constants.StatusFlags.intersection_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem constants.StatusFlags.difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem constants.StatusFlags.remove_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem constants.StatusFlags.symmetric_difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem constants.StatusFlags.toggle_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem constants.StatusFlags.set_spec (self other : constants.StatusFlags) (value : Bool) :
    constants.StatusFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem constants.StatusFlags.complement_spec (self : constants.StatusFlags) :
    constants.StatusFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& statusFlagsAll ⦄ := by
  sorry

end mysql_common
