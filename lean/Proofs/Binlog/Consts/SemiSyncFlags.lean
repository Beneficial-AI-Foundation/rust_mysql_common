import Defs

/-! Statements for `struct SemiSyncFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`semiSyncFlagsAll`). -/
theorem binlog.consts.SemiSyncFlags.all_spec :
    binlog.consts.SemiSyncFlags.all ⦃ r => r.val = semiSyncFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem binlog.consts.SemiSyncFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& semiSyncFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem binlog.consts.SemiSyncFlags.from_bits_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits bits ⦃ r => r = if bits.val &&& semiSyncFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from_spec (val : U8) :
    binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from val ⦃ r =>
      r = if val.val &&& semiSyncFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem binlog.consts.SemiSyncFlags.bits_eq (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.SemiSyncFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem binlog.consts.SemiSyncFlags.empty_spec :
    binlog.consts.SemiSyncFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem binlog.consts.SemiSyncFlags.is_empty_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem binlog.consts.SemiSyncFlags.is_all_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_all self ⦃ b => (b ↔ semiSyncFlagsAll &&& self.val = semiSyncFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem binlog.consts.SemiSyncFlags.intersects_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem binlog.consts.SemiSyncFlags.contains_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem binlog.consts.SemiSyncFlags.union_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem binlog.consts.SemiSyncFlags.insert_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem binlog.consts.SemiSyncFlags.intersection_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem binlog.consts.SemiSyncFlags.difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem binlog.consts.SemiSyncFlags.remove_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem binlog.consts.SemiSyncFlags.symmetric_difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem binlog.consts.SemiSyncFlags.toggle_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem binlog.consts.SemiSyncFlags.set_spec (self other : binlog.consts.SemiSyncFlags) (value : Bool) :
    binlog.consts.SemiSyncFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem binlog.consts.SemiSyncFlags.complement_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& semiSyncFlagsAll ⦄ := by
  sorry

end mysql_common
