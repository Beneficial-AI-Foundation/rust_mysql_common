import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `struct UserVarFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `all`: every flag the crate names (`userVarFlagsAll`). -/
@[step]
theorem binlog.consts.UserVarFlags.all_spec :
    binlog.consts.UserVarFlags.all ⦃ r => r.val = userVarFlagsAll ⦄ := by
  simp [userVarFlags_all_eq, userVarFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem binlog.consts.UserVarFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& userVarFlagsAll ⦄ := by
  simp [binlog.consts.UserVarFlags.from_bits_truncate, userVarFlags_all_eq, lift, userVarFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem binlog.consts.UserVarFlags.from_bits_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits bits ⦃ r => r = if bits.val &&& userVarFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [binlog.consts.UserVarFlags.from_bits, binlog.consts.UserVarFlags.from_bits_truncate, userVarFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, userVarFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from_spec (val : U8) :
    binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from val ⦃ r =>
      r = if val.val &&& userVarFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from, binlog.consts.UserVarFlags.from_bits, binlog.consts.UserVarFlags.from_bits_truncate,
    userVarFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, userVarFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem binlog.consts.UserVarFlags.bits_eq (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.UserVarFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem binlog.consts.UserVarFlags.empty_spec :
    binlog.consts.UserVarFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.UserVarFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem binlog.consts.UserVarFlags.is_empty_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [binlog.consts.UserVarFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem binlog.consts.UserVarFlags.is_all_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_all self ⦃ b => (b ↔ userVarFlagsAll &&& self.val = userVarFlagsAll) ⦄ := by
  simp [binlog.consts.UserVarFlags.is_all, userVarFlags_all_eq, lift, uscalar_eq_iff, userVarFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem binlog.consts.UserVarFlags.intersects_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [binlog.consts.UserVarFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem binlog.consts.UserVarFlags.contains_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [binlog.consts.UserVarFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem binlog.consts.UserVarFlags.union_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem binlog.consts.UserVarFlags.insert_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.insert, binlog.consts.UserVarFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem binlog.consts.UserVarFlags.intersection_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem binlog.consts.UserVarFlags.difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.difference, lift, andNot, u8_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem binlog.consts.UserVarFlags.remove_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.remove, binlog.consts.UserVarFlags.difference, lift, andNot, u8_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem binlog.consts.UserVarFlags.symmetric_difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem binlog.consts.UserVarFlags.toggle_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.UserVarFlags.toggle, binlog.consts.UserVarFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem binlog.consts.UserVarFlags.set_spec (self other : binlog.consts.UserVarFlags) (value : Bool) :
    binlog.consts.UserVarFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  cases value <;> simp [binlog.consts.UserVarFlags.set, binlog.consts.UserVarFlags.insert, binlog.consts.UserVarFlags.union, binlog.consts.UserVarFlags.remove, binlog.consts.UserVarFlags.difference, lift,
    andNot, u8_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem binlog.consts.UserVarFlags.complement_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& userVarFlagsAll ⦄ := by
  simp [binlog.consts.UserVarFlags.complement, binlog.consts.UserVarFlags.from_bits_truncate, userVarFlags_all_eq, lift, complementBits, u8_val_not,
    userVarFlagsAll]

end mysql_common
