import Defs
import Proofs.Util.Constants

/-! Statements for `struct ColumnFlags and its impls` (spec file: `Specs/Constants.lean`). Helper lemmas: `Proofs/Util/Constants.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.ConstUtil

namespace mysql_common

/-- `all`: every flag the crate names (`columnFlagsAll`). -/
@[step]
theorem constants.ColumnFlags.all_spec :
    constants.ColumnFlags.all ⦃ r => r.val = columnFlagsAll ⦄ := by
  simp [columnFlags_all_eq, columnFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem constants.ColumnFlags.from_bits_truncate_spec (bits : U16) :
    constants.ColumnFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& columnFlagsAll ⦄ := by
  simp [constants.ColumnFlags.from_bits_truncate, columnFlags_all_eq, lift, columnFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem constants.ColumnFlags.from_bits_spec (bits : U16) :
    constants.ColumnFlags.from_bits bits ⦃ r => r = if bits.val &&& columnFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [constants.ColumnFlags.from_bits, constants.ColumnFlags.from_bits_truncate, columnFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, columnFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from_spec (val : U16) :
    constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from val ⦃ r =>
      r = if val.val &&& columnFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from, constants.ColumnFlags.from_bits, constants.ColumnFlags.from_bits_truncate,
    columnFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, columnFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem constants.ColumnFlags.bits_eq (self : constants.ColumnFlags) :
    constants.ColumnFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.ColumnFlags.from_bits_retain_eq (bits : U16) :
    constants.ColumnFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem constants.ColumnFlags.empty_spec :
    constants.ColumnFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [constants.ColumnFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem constants.ColumnFlags.is_empty_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [constants.ColumnFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem constants.ColumnFlags.is_all_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_all self ⦃ b => (b ↔ columnFlagsAll &&& self.val = columnFlagsAll) ⦄ := by
  simp [constants.ColumnFlags.is_all, columnFlags_all_eq, lift, uscalar_eq_iff, columnFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem constants.ColumnFlags.intersects_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [constants.ColumnFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem constants.ColumnFlags.contains_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [constants.ColumnFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem constants.ColumnFlags.union_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.ColumnFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem constants.ColumnFlags.insert_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [constants.ColumnFlags.insert, constants.ColumnFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem constants.ColumnFlags.intersection_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [constants.ColumnFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem constants.ColumnFlags.difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [constants.ColumnFlags.difference, lift, andNot, u16_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem constants.ColumnFlags.remove_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [constants.ColumnFlags.remove, constants.ColumnFlags.difference, lift, andNot, u16_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem constants.ColumnFlags.symmetric_difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.ColumnFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem constants.ColumnFlags.toggle_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [constants.ColumnFlags.toggle, constants.ColumnFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem constants.ColumnFlags.set_spec (self other : constants.ColumnFlags) (value : Bool) :
    constants.ColumnFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  cases value <;> simp [constants.ColumnFlags.set, constants.ColumnFlags.insert, constants.ColumnFlags.union, constants.ColumnFlags.remove, constants.ColumnFlags.difference, lift,
    andNot, u16_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem constants.ColumnFlags.complement_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& columnFlagsAll ⦄ := by
  simp only [constants.ColumnFlags.complement, constants.ColumnFlags.from_bits_truncate, columnFlags_all_eq, lift,
    bind_ok, WP.spec_ok, UScalar.val_and, u16_val_not, complementBits, columnFlagsAll]
  simp

/-- `From<ColumnFlags>`: the raw value. -/
theorem U16.Insts.CoreConvertFromColumnFlags.from_eq (val : constants.ColumnFlags) :
    U16.Insts.CoreConvertFromColumnFlags.from val = ok val := by
  rfl

end mysql_common
