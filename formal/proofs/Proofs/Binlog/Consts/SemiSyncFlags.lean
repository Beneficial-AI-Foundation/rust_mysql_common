import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `struct SemiSyncFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `all`: every flag the crate names (`semiSyncFlagsAll`). -/
@[step]
theorem binlog.consts.SemiSyncFlags.all_spec :
    binlog.consts.SemiSyncFlags.all ⦃ r => r.val = semiSyncFlagsAll ⦄ := by
  simp [semiSyncFlags_all_eq, semiSyncFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& semiSyncFlagsAll ⦄ := by
  simp [binlog.consts.SemiSyncFlags.from_bits_truncate, semiSyncFlags_all_eq, lift, semiSyncFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.from_bits_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits bits ⦃ r => r = if bits.val &&& semiSyncFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [binlog.consts.SemiSyncFlags.from_bits, binlog.consts.SemiSyncFlags.from_bits_truncate, semiSyncFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, semiSyncFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from_spec (val : U8) :
    binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from val ⦃ r =>
      r = if val.val &&& semiSyncFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from, binlog.consts.SemiSyncFlags.from_bits, binlog.consts.SemiSyncFlags.from_bits_truncate,
    semiSyncFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, semiSyncFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem binlog.consts.SemiSyncFlags.bits_eq (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.SemiSyncFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem binlog.consts.SemiSyncFlags.empty_spec :
    binlog.consts.SemiSyncFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.SemiSyncFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem binlog.consts.SemiSyncFlags.is_empty_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [binlog.consts.SemiSyncFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem binlog.consts.SemiSyncFlags.is_all_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_all self ⦃ b => (b ↔ semiSyncFlagsAll &&& self.val = semiSyncFlagsAll) ⦄ := by
  simp [binlog.consts.SemiSyncFlags.is_all, semiSyncFlags_all_eq, lift, uscalar_eq_iff, semiSyncFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem binlog.consts.SemiSyncFlags.intersects_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [binlog.consts.SemiSyncFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.contains_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [binlog.consts.SemiSyncFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem binlog.consts.SemiSyncFlags.union_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.insert_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.insert, binlog.consts.SemiSyncFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem binlog.consts.SemiSyncFlags.intersection_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem binlog.consts.SemiSyncFlags.difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.difference, lift, andNot, u8_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.remove_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.remove, binlog.consts.SemiSyncFlags.difference, lift, andNot, u8_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem binlog.consts.SemiSyncFlags.symmetric_difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.toggle_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.SemiSyncFlags.toggle, binlog.consts.SemiSyncFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.set_spec (self other : binlog.consts.SemiSyncFlags) (value : Bool) :
    binlog.consts.SemiSyncFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  cases value <;> simp [binlog.consts.SemiSyncFlags.set, binlog.consts.SemiSyncFlags.insert, binlog.consts.SemiSyncFlags.union, binlog.consts.SemiSyncFlags.remove, binlog.consts.SemiSyncFlags.difference, lift,
    andNot, u8_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem binlog.consts.SemiSyncFlags.complement_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& semiSyncFlagsAll ⦄ := by
  simp [binlog.consts.SemiSyncFlags.complement, binlog.consts.SemiSyncFlags.from_bits_truncate, semiSyncFlags_all_eq, lift, complementBits, u8_val_not,
    semiSyncFlagsAll]

end mysql_common
