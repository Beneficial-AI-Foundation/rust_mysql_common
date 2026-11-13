import Defs

/-! Statements for `struct UserVarFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`userVarFlagsAll`). -/
theorem binlog.consts.UserVarFlags.all_spec :
    binlog.consts.UserVarFlags.all ⦃ r => r.val = userVarFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem binlog.consts.UserVarFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& userVarFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem binlog.consts.UserVarFlags.from_bits_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits bits ⦃ r => r = if bits.val &&& userVarFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from_spec (val : U8) :
    binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from val ⦃ r =>
      r = if val.val &&& userVarFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem binlog.consts.UserVarFlags.bits_eq (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.UserVarFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem binlog.consts.UserVarFlags.empty_spec :
    binlog.consts.UserVarFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem binlog.consts.UserVarFlags.is_empty_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem binlog.consts.UserVarFlags.is_all_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_all self ⦃ b => (b ↔ userVarFlagsAll &&& self.val = userVarFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem binlog.consts.UserVarFlags.intersects_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem binlog.consts.UserVarFlags.contains_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem binlog.consts.UserVarFlags.union_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem binlog.consts.UserVarFlags.insert_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem binlog.consts.UserVarFlags.intersection_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem binlog.consts.UserVarFlags.difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem binlog.consts.UserVarFlags.remove_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem binlog.consts.UserVarFlags.symmetric_difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem binlog.consts.UserVarFlags.toggle_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem binlog.consts.UserVarFlags.set_spec (self other : binlog.consts.UserVarFlags) (value : Bool) :
    binlog.consts.UserVarFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem binlog.consts.UserVarFlags.complement_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& userVarFlagsAll ⦄ := by
  sorry

end mysql_common
