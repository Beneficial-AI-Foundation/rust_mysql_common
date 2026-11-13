import Defs

/-! Statements for `struct EventFlags and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `all`: every flag the crate names (`eventFlagsAll`). -/
theorem binlog.consts.EventFlags.all_spec :
    binlog.consts.EventFlags.all ⦃ r => r.val = eventFlagsAll ⦄ := by
  sorry

/-- `from_bits_truncate`: the known bits of `bits`. -/
theorem binlog.consts.EventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& eventFlagsAll ⦄ := by
  sorry

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
theorem binlog.consts.EventFlags.from_bits_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits bits ⦃ r => r = if bits.val &&& eventFlagsAll = bits.val then some bits else none ⦄ := by
  sorry

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
theorem binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from_spec (val : U16) :
    binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from val ⦃ r =>
      r = if val.val &&& eventFlagsAll = val.val then .Ok val else .Err val ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem binlog.consts.EventFlags.bits_eq (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.bits self = ok self := by
  sorry

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
theorem binlog.consts.EventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.EventFlags.from_bits_retain bits = ok bits := by
  sorry

/-- `empty`: no flags. -/
theorem binlog.consts.EventFlags.empty_spec :
    binlog.consts.EventFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `is_empty`: no bit set. -/
theorem binlog.consts.EventFlags.is_empty_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄ := by
  sorry

/-- `is_all`: every known flag set. -/
theorem binlog.consts.EventFlags.is_all_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_all self ⦃ b => (b ↔ eventFlagsAll &&& self.val = eventFlagsAll) ⦄ := by
  sorry

/-- `intersects`: a common bit. -/
theorem binlog.consts.EventFlags.intersects_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄ := by
  sorry

/-- `contains`: every bit of `other` is in `self`. -/
theorem binlog.consts.EventFlags.contains_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄ := by
  sorry

/-- `union`: the bits of either. -/
theorem binlog.consts.EventFlags.union_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `insert`: `union`. -/
theorem binlog.consts.EventFlags.insert_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄ := by
  sorry

/-- `intersection`: the common bits. -/
theorem binlog.consts.EventFlags.intersection_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄ := by
  sorry

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
theorem binlog.consts.EventFlags.difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `remove`: `difference`. -/
theorem binlog.consts.EventFlags.remove_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄ := by
  sorry

/-- `symmetric_difference`: the bits in exactly one. -/
theorem binlog.consts.EventFlags.symmetric_difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `toggle`: `symmetric_difference`. -/
theorem binlog.consts.EventFlags.toggle_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄ := by
  sorry

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
theorem binlog.consts.EventFlags.set_spec (self other : binlog.consts.EventFlags) (value : Bool) :
    binlog.consts.EventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄ := by
  sorry

/-- `complement`: the known flags not in `self`. -/
theorem binlog.consts.EventFlags.complement_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& eventFlagsAll ⦄ := by
  sorry

end mysql_common
