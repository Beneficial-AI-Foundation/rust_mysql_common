import Defs
import Proofs.Util.Constants

/-! Statements for `struct StatusFlags and its impls` (spec file: `Specs/Constants.lean`). Helper lemmas: `Proofs/Util/Constants.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.ConstUtil

namespace mysql_common

/-- `all`: every flag the crate names (`statusFlagsAll`). -/
@[step]
theorem constants.StatusFlags.all_spec :
    constants.StatusFlags.all ⦃ r => r.val = statusFlagsAll ⦄ := by
  simp [statusFlags_all_eq, statusFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem constants.StatusFlags.from_bits_truncate_spec (bits : U16) :
    constants.StatusFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& statusFlagsAll ⦄ := by
  simp [constants.StatusFlags.from_bits_truncate, statusFlags_all_eq, lift, statusFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem constants.StatusFlags.from_bits_spec (bits : U16) :
    constants.StatusFlags.from_bits bits ⦃ r => r = if bits.val &&& statusFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [constants.StatusFlags.from_bits, constants.StatusFlags.from_bits_truncate, statusFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, statusFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from_spec (val : U16) :
    constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from val ⦃ r =>
      r = if val.val &&& statusFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from, constants.StatusFlags.from_bits, constants.StatusFlags.from_bits_truncate,
    statusFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, statusFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem constants.StatusFlags.bits_eq (self : constants.StatusFlags) :
    constants.StatusFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.StatusFlags.from_bits_retain_eq (bits : U16) :
    constants.StatusFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem constants.StatusFlags.empty_spec :
    constants.StatusFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [constants.StatusFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem constants.StatusFlags.is_empty_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [constants.StatusFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem constants.StatusFlags.is_all_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_all self ⦃ b => (b ↔ statusFlagsAll &&& self.val = statusFlagsAll) ⦄ := by
  simp [constants.StatusFlags.is_all, statusFlags_all_eq, lift, uscalar_eq_iff, statusFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem constants.StatusFlags.intersects_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [constants.StatusFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem constants.StatusFlags.contains_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [constants.StatusFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem constants.StatusFlags.union_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.StatusFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem constants.StatusFlags.insert_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.StatusFlags.insert, constants.StatusFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem constants.StatusFlags.intersection_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [constants.StatusFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem constants.StatusFlags.difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [constants.StatusFlags.difference, lift, andNot, u16_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem constants.StatusFlags.remove_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [constants.StatusFlags.remove, constants.StatusFlags.difference, lift, andNot, u16_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem constants.StatusFlags.symmetric_difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.StatusFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem constants.StatusFlags.toggle_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.StatusFlags.toggle, constants.StatusFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem constants.StatusFlags.set_spec (self other : constants.StatusFlags) (value : Bool) :
    constants.StatusFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  cases value <;> simp [constants.StatusFlags.set, constants.StatusFlags.insert, constants.StatusFlags.union, constants.StatusFlags.remove, constants.StatusFlags.difference, lift,
    andNot, u16_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem constants.StatusFlags.complement_spec (self : constants.StatusFlags) :
    constants.StatusFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& statusFlagsAll ⦄ := by
  simp [constants.StatusFlags.complement, constants.StatusFlags.from_bits_truncate, statusFlags_all_eq, lift, complementBits, u16_val_not,
    statusFlagsAll]

end mysql_common
