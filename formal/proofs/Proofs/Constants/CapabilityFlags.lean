import Defs
import Proofs.Util.Constants

/-! Statements for `struct CapabilityFlags and its impls` (spec file: `Specs/Constants.lean`). Helper lemmas: `Proofs/Util/Constants.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.ConstUtil

namespace mysql_common

/-- `all`: every flag the crate names (`capabilityFlagsAll`). -/
@[step]
theorem constants.CapabilityFlags.all_spec :
    constants.CapabilityFlags.all ⦃ r => r.val = capabilityFlagsAll ⦄ := by
  simp [capabilityFlags_all_eq, capabilityFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem constants.CapabilityFlags.from_bits_truncate_spec (bits : U32) :
    constants.CapabilityFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& capabilityFlagsAll ⦄ := by
  simp [constants.CapabilityFlags.from_bits_truncate, capabilityFlags_all_eq, lift, capabilityFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem constants.CapabilityFlags.from_bits_spec (bits : U32) :
    constants.CapabilityFlags.from_bits bits ⦃ r => r = if bits.val &&& capabilityFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [constants.CapabilityFlags.from_bits, constants.CapabilityFlags.from_bits_truncate, capabilityFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, capabilityFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from_spec (val : U32) :
    constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from val ⦃ r =>
      r = if val.val &&& capabilityFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from, constants.CapabilityFlags.from_bits, constants.CapabilityFlags.from_bits_truncate,
    capabilityFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, capabilityFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem constants.CapabilityFlags.bits_eq (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.CapabilityFlags.from_bits_retain_eq (bits : U32) :
    constants.CapabilityFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem constants.CapabilityFlags.empty_spec :
    constants.CapabilityFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [constants.CapabilityFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem constants.CapabilityFlags.is_empty_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [constants.CapabilityFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem constants.CapabilityFlags.is_all_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_all self ⦃ b => (b ↔ capabilityFlagsAll &&& self.val = capabilityFlagsAll) ⦄ := by
  simp [constants.CapabilityFlags.is_all, capabilityFlags_all_eq, lift, uscalar_eq_iff, capabilityFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem constants.CapabilityFlags.intersects_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [constants.CapabilityFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem constants.CapabilityFlags.contains_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [constants.CapabilityFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem constants.CapabilityFlags.union_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.CapabilityFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem constants.CapabilityFlags.insert_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.CapabilityFlags.insert, constants.CapabilityFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem constants.CapabilityFlags.intersection_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [constants.CapabilityFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem constants.CapabilityFlags.difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.difference self other ⦃ r => r.val = andNot 32 self.val other.val ⦄ := by
  simp [constants.CapabilityFlags.difference, lift, andNot, u32_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem constants.CapabilityFlags.remove_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.remove self other ⦃ r => r.val = andNot 32 self.val other.val ⦄ := by
  simp [constants.CapabilityFlags.remove, constants.CapabilityFlags.difference, lift, andNot, u32_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem constants.CapabilityFlags.symmetric_difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.CapabilityFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem constants.CapabilityFlags.toggle_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.CapabilityFlags.toggle, constants.CapabilityFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem constants.CapabilityFlags.set_spec (self other : constants.CapabilityFlags) (value : Bool) :
    constants.CapabilityFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 32 self.val other.val ⦄ := by
  cases value <;> simp [constants.CapabilityFlags.set, constants.CapabilityFlags.insert, constants.CapabilityFlags.union, constants.CapabilityFlags.remove, constants.CapabilityFlags.difference, lift,
    andNot, u32_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem constants.CapabilityFlags.complement_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.complement self ⦃ r => r.val = complementBits 32 self.val &&& capabilityFlagsAll ⦄ := by
  simp only [constants.CapabilityFlags.complement, constants.CapabilityFlags.from_bits_truncate, capabilityFlags_all_eq, lift,
    bind_ok, WP.spec_ok, UScalar.val_and, u32_val_not, complementBits, capabilityFlagsAll]
  simp

end mysql_common
