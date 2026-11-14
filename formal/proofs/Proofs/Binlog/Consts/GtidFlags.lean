import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `struct GtidFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `all`: every flag the crate names (`gtidFlagsAll`). -/
@[step]
theorem binlog.consts.GtidFlags.all_spec :
    binlog.consts.GtidFlags.all ⦃ r => r.val = gtidFlagsAll ⦄ := by
  simp [gtidFlags_all_eq, gtidFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem binlog.consts.GtidFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& gtidFlagsAll ⦄ := by
  simp [binlog.consts.GtidFlags.from_bits_truncate, gtidFlags_all_eq, lift, gtidFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem binlog.consts.GtidFlags.from_bits_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits bits ⦃ r => r = if bits.val &&& gtidFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [binlog.consts.GtidFlags.from_bits, binlog.consts.GtidFlags.from_bits_truncate, gtidFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, gtidFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from_spec (val : U8) :
    binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from val ⦃ r =>
      r = if val.val &&& gtidFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from, binlog.consts.GtidFlags.from_bits, binlog.consts.GtidFlags.from_bits_truncate,
    gtidFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, gtidFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem binlog.consts.GtidFlags.bits_eq (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.GtidFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.GtidFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem binlog.consts.GtidFlags.empty_spec :
    binlog.consts.GtidFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.GtidFlags.empty]

/-- `Default`: no flags. -/
@[step]
theorem binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default_spec :
    binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default, binlog.consts.GtidFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem binlog.consts.GtidFlags.is_empty_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [binlog.consts.GtidFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem binlog.consts.GtidFlags.is_all_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_all self ⦃ b => (b ↔ gtidFlagsAll &&& self.val = gtidFlagsAll) ⦄ := by
  simp [binlog.consts.GtidFlags.is_all, gtidFlags_all_eq, lift, uscalar_eq_iff, gtidFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem binlog.consts.GtidFlags.intersects_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [binlog.consts.GtidFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem binlog.consts.GtidFlags.contains_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [binlog.consts.GtidFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem binlog.consts.GtidFlags.union_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.GtidFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem binlog.consts.GtidFlags.insert_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.GtidFlags.insert, binlog.consts.GtidFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem binlog.consts.GtidFlags.intersection_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [binlog.consts.GtidFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem binlog.consts.GtidFlags.difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.GtidFlags.difference, lift, andNot, u8_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem binlog.consts.GtidFlags.remove_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄ := by
  simp [binlog.consts.GtidFlags.remove, binlog.consts.GtidFlags.difference, lift, andNot, u8_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem binlog.consts.GtidFlags.symmetric_difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.GtidFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem binlog.consts.GtidFlags.toggle_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.GtidFlags.toggle, binlog.consts.GtidFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem binlog.consts.GtidFlags.set_spec (self other : binlog.consts.GtidFlags) (value : Bool) :
    binlog.consts.GtidFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄ := by
  cases value <;> simp [binlog.consts.GtidFlags.set, binlog.consts.GtidFlags.insert, binlog.consts.GtidFlags.union, binlog.consts.GtidFlags.remove, binlog.consts.GtidFlags.difference, lift,
    andNot, u8_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem binlog.consts.GtidFlags.complement_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& gtidFlagsAll ⦄ := by
  simp [binlog.consts.GtidFlags.complement, binlog.consts.GtidFlags.from_bits_truncate, gtidFlags_all_eq, lift, complementBits, u8_val_not,
    gtidFlagsAll]

end mysql_common
