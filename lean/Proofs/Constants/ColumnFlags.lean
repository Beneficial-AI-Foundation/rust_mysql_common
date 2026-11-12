import Defs

/-! Statements for `struct ColumnFlags and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`columnFlagsAll`). -/
theorem constants.ColumnFlags.all_spec :
    constants.ColumnFlags.all ⦃ r => r.val = columnFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem constants.ColumnFlags.from_bits_truncate_spec (bits : U16) :
    constants.ColumnFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& columnFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem constants.ColumnFlags.from_bits_spec (bits : U16) :
    constants.ColumnFlags.from_bits bits ⦃ r => r = if bits.val &&& columnFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from_spec (val : U16) :
    constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from val ⦃ r =>
      r = if val.val &&& columnFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem constants.ColumnFlags.bits_eq (self : constants.ColumnFlags) :
    constants.ColumnFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem constants.ColumnFlags.from_bits_retain_eq (bits : U16) :
    constants.ColumnFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem constants.ColumnFlags.empty_spec :
    constants.ColumnFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem constants.ColumnFlags.is_empty_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem constants.ColumnFlags.is_all_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_all self ⦃ b => (b ↔ columnFlagsAll &&& self.val = columnFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem constants.ColumnFlags.intersects_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem constants.ColumnFlags.contains_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem constants.ColumnFlags.union_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem constants.ColumnFlags.insert_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem constants.ColumnFlags.intersection_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem constants.ColumnFlags.difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem constants.ColumnFlags.remove_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem constants.ColumnFlags.symmetric_difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem constants.ColumnFlags.toggle_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem constants.ColumnFlags.set_spec (self other : constants.ColumnFlags) (value : Bool) :
    constants.ColumnFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem constants.ColumnFlags.complement_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& columnFlagsAll ⦄ := by
  sorry

/-- `From<ColumnFlags>`: the raw value. -/
theorem U16.Insts.CoreConvertFromColumnFlags.from_eq (val : constants.ColumnFlags) :
    U16.Insts.CoreConvertFromColumnFlags.from val = ok val := by
  sorry

end mysql_common
