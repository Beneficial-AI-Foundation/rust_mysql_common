import Defs

/-! Statements for `struct RowsEventFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`rowsEventFlagsAll`). -/
theorem binlog.consts.RowsEventFlags.all_spec :
    binlog.consts.RowsEventFlags.all ⦃ r => r.val = rowsEventFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem binlog.consts.RowsEventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& rowsEventFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem binlog.consts.RowsEventFlags.from_bits_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits bits ⦃ r => r = if bits.val &&& rowsEventFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from_spec (val : U16) :
    binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from val ⦃ r =>
      r = if val.val &&& rowsEventFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem binlog.consts.RowsEventFlags.bits_eq (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.RowsEventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem binlog.consts.RowsEventFlags.empty_spec :
    binlog.consts.RowsEventFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem binlog.consts.RowsEventFlags.is_empty_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem binlog.consts.RowsEventFlags.is_all_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_all self ⦃ b => (b ↔ rowsEventFlagsAll &&& self.val = rowsEventFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem binlog.consts.RowsEventFlags.intersects_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem binlog.consts.RowsEventFlags.contains_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem binlog.consts.RowsEventFlags.union_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem binlog.consts.RowsEventFlags.insert_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem binlog.consts.RowsEventFlags.intersection_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem binlog.consts.RowsEventFlags.difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem binlog.consts.RowsEventFlags.remove_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem binlog.consts.RowsEventFlags.symmetric_difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem binlog.consts.RowsEventFlags.toggle_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem binlog.consts.RowsEventFlags.set_spec (self other : binlog.consts.RowsEventFlags) (value : Bool) :
    binlog.consts.RowsEventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem binlog.consts.RowsEventFlags.complement_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& rowsEventFlagsAll ⦄ := by
  sorry

end mysql_common
