import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `struct RowsEventFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `all`: every flag the crate names (`rowsEventFlagsAll`). -/
@[step]
theorem binlog.consts.RowsEventFlags.all_spec :
    binlog.consts.RowsEventFlags.all ⦃ r => r.val = rowsEventFlagsAll ⦄ := by
  simp [rowsEventFlags_all_eq, rowsEventFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem binlog.consts.RowsEventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& rowsEventFlagsAll ⦄ := by
  simp [binlog.consts.RowsEventFlags.from_bits_truncate, rowsEventFlags_all_eq, lift, rowsEventFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem binlog.consts.RowsEventFlags.from_bits_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits bits ⦃ r => r = if bits.val &&& rowsEventFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [binlog.consts.RowsEventFlags.from_bits, binlog.consts.RowsEventFlags.from_bits_truncate, rowsEventFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, rowsEventFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from_spec (val : U16) :
    binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from val ⦃ r =>
      r = if val.val &&& rowsEventFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from, binlog.consts.RowsEventFlags.from_bits, binlog.consts.RowsEventFlags.from_bits_truncate,
    rowsEventFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, rowsEventFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem binlog.consts.RowsEventFlags.bits_eq (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.RowsEventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem binlog.consts.RowsEventFlags.empty_spec :
    binlog.consts.RowsEventFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.RowsEventFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem binlog.consts.RowsEventFlags.is_empty_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [binlog.consts.RowsEventFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem binlog.consts.RowsEventFlags.is_all_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_all self ⦃ b => (b ↔ rowsEventFlagsAll &&& self.val = rowsEventFlagsAll) ⦄ := by
  simp [binlog.consts.RowsEventFlags.is_all, rowsEventFlags_all_eq, lift, uscalar_eq_iff, rowsEventFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem binlog.consts.RowsEventFlags.intersects_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [binlog.consts.RowsEventFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem binlog.consts.RowsEventFlags.contains_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [binlog.consts.RowsEventFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem binlog.consts.RowsEventFlags.union_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem binlog.consts.RowsEventFlags.insert_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.insert, binlog.consts.RowsEventFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem binlog.consts.RowsEventFlags.intersection_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem binlog.consts.RowsEventFlags.difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.difference, lift, andNot, u16_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem binlog.consts.RowsEventFlags.remove_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.remove, binlog.consts.RowsEventFlags.difference, lift, andNot, u16_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem binlog.consts.RowsEventFlags.symmetric_difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem binlog.consts.RowsEventFlags.toggle_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.RowsEventFlags.toggle, binlog.consts.RowsEventFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem binlog.consts.RowsEventFlags.set_spec (self other : binlog.consts.RowsEventFlags) (value : Bool) :
    binlog.consts.RowsEventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  cases value <;> simp [binlog.consts.RowsEventFlags.set, binlog.consts.RowsEventFlags.insert, binlog.consts.RowsEventFlags.union, binlog.consts.RowsEventFlags.remove, binlog.consts.RowsEventFlags.difference, lift,
    andNot, u16_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem binlog.consts.RowsEventFlags.complement_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& rowsEventFlagsAll ⦄ := by
  simp [binlog.consts.RowsEventFlags.complement, binlog.consts.RowsEventFlags.from_bits_truncate, rowsEventFlags_all_eq, lift, complementBits, u16_val_not,
    rowsEventFlagsAll]

end mysql_common
