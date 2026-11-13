import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `struct EventFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `all`: every flag the crate names (`eventFlagsAll`). -/
@[step]
theorem binlog.consts.EventFlags.all_spec :
    binlog.consts.EventFlags.all ⦃ r => r.val = eventFlagsAll ⦄ := by
  simp [eventFlags_all_eq, eventFlagsAll]

/-- `from_bits_truncate`: the known bits of `bits`. -/
@[step]
theorem binlog.consts.EventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& eventFlagsAll ⦄ := by
  simp [binlog.consts.EventFlags.from_bits_truncate, eventFlags_all_eq, lift, eventFlagsAll]

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
@[step]
theorem binlog.consts.EventFlags.from_bits_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits bits ⦃ r => r = if bits.val &&& eventFlagsAll = bits.val then some bits else none ⦄ := by
  simp only [binlog.consts.EventFlags.from_bits, binlog.consts.EventFlags.from_bits_truncate, eventFlags_all_eq, lift, bind_ok,
    uscalar_eq_iff, UScalar.val_and, eventFlagsAll]
  split <;> simp_all

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
@[step]
theorem binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from_spec (val : U16) :
    binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from val ⦃ r =>
      r = if val.val &&& eventFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  simp only [binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from, binlog.consts.EventFlags.from_bits, binlog.consts.EventFlags.from_bits_truncate,
    eventFlags_all_eq, lift, bind_ok, uscalar_eq_iff, UScalar.val_and, eventFlagsAll]
  split <;> simp_all

/-- `bits`: the raw value. -/
theorem binlog.consts.EventFlags.bits_eq (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.bits self = ok self := by
  rfl

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.EventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.EventFlags.from_bits_retain bits = ok bits := by
  rfl

/-- `empty`: no flags. -/
@[step]
theorem binlog.consts.EventFlags.empty_spec :
    binlog.consts.EventFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [binlog.consts.EventFlags.empty]

/-- `is_empty`: no bit set. -/
@[step]
theorem binlog.consts.EventFlags.is_empty_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  simp [binlog.consts.EventFlags.is_empty, uscalar_eq_iff]

/-- `is_all`: every known flag set. -/
@[step]
theorem binlog.consts.EventFlags.is_all_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_all self ⦃ b => (b ↔ eventFlagsAll &&& self.val = eventFlagsAll) ⦄ := by
  simp [binlog.consts.EventFlags.is_all, eventFlags_all_eq, lift, uscalar_eq_iff, eventFlagsAll, nat_or_eq_iff_and_eq]

/-- `intersects`: a common bit. -/
@[step]
theorem binlog.consts.EventFlags.intersects_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  simp [binlog.consts.EventFlags.intersects, lift]

/-- `contains`: every bit of `other` is in `self`. -/
@[step]
theorem binlog.consts.EventFlags.contains_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  simp [binlog.consts.EventFlags.contains, lift, uscalar_eq_iff]

/-- `union`: the bits of either. -/
@[step]
theorem binlog.consts.EventFlags.union_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.EventFlags.union, lift]

/-- `insert`: `union`. -/
@[step]
theorem binlog.consts.EventFlags.insert_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  simp [binlog.consts.EventFlags.insert, binlog.consts.EventFlags.union, lift]

/-- `intersection`: the common bits. -/
@[step]
theorem binlog.consts.EventFlags.intersection_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  simp [binlog.consts.EventFlags.intersection, lift]

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
@[step]
theorem binlog.consts.EventFlags.difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [binlog.consts.EventFlags.difference, lift, andNot, u16_val_not]

/-- `remove`: `difference`. -/
@[step]
theorem binlog.consts.EventFlags.remove_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  simp [binlog.consts.EventFlags.remove, binlog.consts.EventFlags.difference, lift, andNot, u16_val_not]

/-- `symmetric_difference`: the bits in exactly one. -/
@[step]
theorem binlog.consts.EventFlags.symmetric_difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.EventFlags.symmetric_difference, lift]

/-- `toggle`: `symmetric_difference`. -/
@[step]
theorem binlog.consts.EventFlags.toggle_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  simp [binlog.consts.EventFlags.toggle, binlog.consts.EventFlags.symmetric_difference, lift]

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
@[step]
theorem binlog.consts.EventFlags.set_spec (self other : binlog.consts.EventFlags) (value : Bool) :
    binlog.consts.EventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  cases value <;> simp [binlog.consts.EventFlags.set, binlog.consts.EventFlags.insert, binlog.consts.EventFlags.union, binlog.consts.EventFlags.remove, binlog.consts.EventFlags.difference, lift,
    andNot, u16_val_not]

/-- `complement`: the known flags not in `self`. -/
@[step]
theorem binlog.consts.EventFlags.complement_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& eventFlagsAll ⦄ := by
  simp [binlog.consts.EventFlags.complement, binlog.consts.EventFlags.from_bits_truncate, eventFlags_all_eq, lift, complementBits, u16_val_not,
    eventFlagsAll]

end mysql_common
