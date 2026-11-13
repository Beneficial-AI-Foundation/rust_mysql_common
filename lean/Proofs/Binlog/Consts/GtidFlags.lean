import Defs

/-! Statements for `struct GtidFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`gtidFlagsAll`). -/
theorem binlog.consts.GtidFlags.all_spec :
    binlog.consts.GtidFlags.all ⦃ r => r.val = gtidFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem binlog.consts.GtidFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& gtidFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem binlog.consts.GtidFlags.from_bits_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits bits ⦃ r => r = if bits.val &&& gtidFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from_spec (val : U8) :
    binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from val ⦃ r =>
      r = if val.val &&& gtidFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem binlog.consts.GtidFlags.bits_eq (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.GtidFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.GtidFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem binlog.consts.GtidFlags.empty_spec :
    binlog.consts.GtidFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `Default`: no flags. -/
theorem binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default_spec :
    binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem binlog.consts.GtidFlags.is_empty_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem binlog.consts.GtidFlags.is_all_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_all self ⦃ b => (b ↔ gtidFlagsAll &&& self.val = gtidFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem binlog.consts.GtidFlags.intersects_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem binlog.consts.GtidFlags.contains_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem binlog.consts.GtidFlags.union_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem binlog.consts.GtidFlags.insert_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem binlog.consts.GtidFlags.intersection_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem binlog.consts.GtidFlags.difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem binlog.consts.GtidFlags.remove_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem binlog.consts.GtidFlags.symmetric_difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem binlog.consts.GtidFlags.toggle_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem binlog.consts.GtidFlags.set_spec (self other : binlog.consts.GtidFlags) (value : Bool) :
    binlog.consts.GtidFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem binlog.consts.GtidFlags.complement_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& gtidFlagsAll ⦄ := by
  sorry

end mysql_common
