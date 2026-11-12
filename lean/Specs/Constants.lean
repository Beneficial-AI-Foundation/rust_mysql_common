import Proofs.Constants.ColumnType
import Proofs.Constants.StatusFlags
import Proofs.Constants.CapabilityFlags
import Proofs.Constants.ColumnFlags
import Proofs.Constants.CursorType
import Proofs.Constants.StmtExecuteParamsFlags
import Proofs.Constants.StmtExecuteParamFlags

/-!
# `src/constants.rs`
    The parts of `src/constants.rs` used by stages c–f: the column type codes (`ColumnType`,
    `TryFrom<u8>`, `From<ColumnType> for u8`) and the flag words `StatusFlags`, `CapabilityFlags`,
    `ColumnFlags`, `CursorType`, `StmtExecuteParamsFlags`, `StmtExecuteParamFlags`.

    **Patch.** The flag types are plain `#[repr(transparent)]` structs with the `bitflags` 2.13 API
    written out (translation patch 20); Aeneas models each as its raw integer (`StatusFlags := U16`,
    ...). The statements are about the patched code; the patch header argues that it behaves as
    the `bitflags!` original.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Flags.lean` (`columnTypeCode`, `columnTypeOfCode`,
    `statusFlagsAll`, `capabilityFlagsAll`, `columnFlagsAll`, `andNot`, `complementBits`).

    **Not covered.** The named flag constants (plain definitions), `ColumnType::is_*_type`
    (classification helpers), `Debug`/`Display` impls, the iterators and operator impls of the flag
    types (not translated), the other constants of the file (later stages).

    **Behaviour to note.** `StatusFlags::from_bits` (hence `TryFrom<u16>`) rejects bit 2 (value 4),
    which MySQL does not assign: an OK or EOF packet whose status has that bit fails to parse.
    Code 244 (MySQL's `MYSQL_TYPE_BOOL` placeholder) is not a `ColumnType`: a column definition with
    it fails to parse.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum ColumnType and its impls` -/

/-- `TryFrom<u8> for ColumnType`: the type with that code, or the code back as the error. -/
recall constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec (value : U8) :
    constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from value =
      ok (match columnTypeOfCode value.val with
        | some ct => .Ok ct
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec`

/-- `From<ColumnType> for u8`: the type code. -/
recall U8.Insts.CoreConvertFromColumnType.from_spec (ct : constants.ColumnType) :
    U8.Insts.CoreConvertFromColumnType.from ct ⦃ r => r.val = columnTypeCode ct ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.CoreConvertFromColumnType.from_spec`

/-! ### `struct StatusFlags and its impls` -/

/-- `all`: every flag the crate names (`statusFlagsAll`). -/
recall constants.StatusFlags.all_spec :
    constants.StatusFlags.all ⦃ r => r.val = statusFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.all_spec`

/-- `from_bits_truncate`: the known bits of `bits`. -/
recall constants.StatusFlags.from_bits_truncate_spec (bits : U16) :
    constants.StatusFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& statusFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.from_bits_truncate_spec`

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall constants.StatusFlags.from_bits_spec (bits : U16) :
    constants.StatusFlags.from_bits bits ⦃ r => r = if bits.val &&& statusFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.from_bits_spec`

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from_spec (val : U16) :
    constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from val ⦃ r =>
      r = if val.val &&& statusFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from_spec`

/-- `bits`: the raw value. -/
recall constants.StatusFlags.bits_eq (self : constants.StatusFlags) :
    constants.StatusFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.bits_eq`

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall constants.StatusFlags.from_bits_retain_eq (bits : U16) :
    constants.StatusFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.from_bits_retain_eq`

/-- `empty`: no flags. -/
recall constants.StatusFlags.empty_spec :
    constants.StatusFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.empty_spec`

/-- `is_empty`: no bit set. -/
recall constants.StatusFlags.is_empty_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.is_empty_spec`

/-- `is_all`: every known flag set. -/
recall constants.StatusFlags.is_all_spec (self : constants.StatusFlags) :
    constants.StatusFlags.is_all self ⦃ b => (b ↔ statusFlagsAll &&& self.val = statusFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.is_all_spec`

/-- `intersects`: a common bit. -/
recall constants.StatusFlags.intersects_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.intersects_spec`

/-- `contains`: every bit of `other` is in `self`. -/
recall constants.StatusFlags.contains_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.contains_spec`

/-- `union`: the bits of either. -/
recall constants.StatusFlags.union_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.union_spec`

/-- `insert`: `union`. -/
recall constants.StatusFlags.insert_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.insert_spec`

/-- `intersection`: the common bits. -/
recall constants.StatusFlags.intersection_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.intersection_spec`

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall constants.StatusFlags.difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.difference_spec`

/-- `remove`: `difference`. -/
recall constants.StatusFlags.remove_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.remove_spec`

/-- `symmetric_difference`: the bits in exactly one. -/
recall constants.StatusFlags.symmetric_difference_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.symmetric_difference_spec`

/-- `toggle`: `symmetric_difference`. -/
recall constants.StatusFlags.toggle_spec (self other : constants.StatusFlags) :
    constants.StatusFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.toggle_spec`

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall constants.StatusFlags.set_spec (self other : constants.StatusFlags) (value : Bool) :
    constants.StatusFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.set_spec`

/-- `complement`: the known flags not in `self`. -/
recall constants.StatusFlags.complement_spec (self : constants.StatusFlags) :
    constants.StatusFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& statusFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StatusFlags.complement_spec`

/-! ### `struct CapabilityFlags and its impls` -/

/-- `all`: every flag the crate names (`capabilityFlagsAll`). -/
recall constants.CapabilityFlags.all_spec :
    constants.CapabilityFlags.all ⦃ r => r.val = capabilityFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.all_spec`

/-- `from_bits_truncate`: the known bits of `bits`. -/
recall constants.CapabilityFlags.from_bits_truncate_spec (bits : U32) :
    constants.CapabilityFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& capabilityFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.from_bits_truncate_spec`

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall constants.CapabilityFlags.from_bits_spec (bits : U32) :
    constants.CapabilityFlags.from_bits bits ⦃ r => r = if bits.val &&& capabilityFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.from_bits_spec`

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from_spec (val : U32) :
    constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from val ⦃ r =>
      r = if val.val &&& capabilityFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.Insts.CoreConvertTryFromU32UnknownCapabilityFlags.try_from_spec`

/-- `bits`: the raw value. -/
recall constants.CapabilityFlags.bits_eq (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.bits_eq`

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall constants.CapabilityFlags.from_bits_retain_eq (bits : U32) :
    constants.CapabilityFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.from_bits_retain_eq`

/-- `empty`: no flags. -/
recall constants.CapabilityFlags.empty_spec :
    constants.CapabilityFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.empty_spec`

/-- `is_empty`: no bit set. -/
recall constants.CapabilityFlags.is_empty_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.is_empty_spec`

/-- `is_all`: every known flag set. -/
recall constants.CapabilityFlags.is_all_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.is_all self ⦃ b => (b ↔ capabilityFlagsAll &&& self.val = capabilityFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.is_all_spec`

/-- `intersects`: a common bit. -/
recall constants.CapabilityFlags.intersects_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.intersects_spec`

/-- `contains`: every bit of `other` is in `self`. -/
recall constants.CapabilityFlags.contains_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.contains_spec`

/-- `union`: the bits of either. -/
recall constants.CapabilityFlags.union_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.union_spec`

/-- `insert`: `union`. -/
recall constants.CapabilityFlags.insert_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.insert_spec`

/-- `intersection`: the common bits. -/
recall constants.CapabilityFlags.intersection_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.intersection_spec`

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall constants.CapabilityFlags.difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.difference self other ⦃ r => r.val = andNot 32 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.difference_spec`

/-- `remove`: `difference`. -/
recall constants.CapabilityFlags.remove_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.remove self other ⦃ r => r.val = andNot 32 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.remove_spec`

/-- `symmetric_difference`: the bits in exactly one. -/
recall constants.CapabilityFlags.symmetric_difference_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.symmetric_difference_spec`

/-- `toggle`: `symmetric_difference`. -/
recall constants.CapabilityFlags.toggle_spec (self other : constants.CapabilityFlags) :
    constants.CapabilityFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.toggle_spec`

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall constants.CapabilityFlags.set_spec (self other : constants.CapabilityFlags) (value : Bool) :
    constants.CapabilityFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 32 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.set_spec`

/-- `complement`: the known flags not in `self`. -/
recall constants.CapabilityFlags.complement_spec (self : constants.CapabilityFlags) :
    constants.CapabilityFlags.complement self ⦃ r => r.val = complementBits 32 self.val &&& capabilityFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CapabilityFlags.complement_spec`

/-! ### `struct ColumnFlags and its impls` -/

/-- `all`: every flag the crate names (`columnFlagsAll`). -/
recall constants.ColumnFlags.all_spec :
    constants.ColumnFlags.all ⦃ r => r.val = columnFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.all_spec`

/-- `from_bits_truncate`: the known bits of `bits`. -/
recall constants.ColumnFlags.from_bits_truncate_spec (bits : U16) :
    constants.ColumnFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& columnFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.from_bits_truncate_spec`

/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall constants.ColumnFlags.from_bits_spec (bits : U16) :
    constants.ColumnFlags.from_bits bits ⦃ r => r = if bits.val &&& columnFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.from_bits_spec`

/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from_spec (val : U16) :
    constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from val ⦃ r =>
      r = if val.val &&& columnFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from_spec`

/-- `bits`: the raw value. -/
recall constants.ColumnFlags.bits_eq (self : constants.ColumnFlags) :
    constants.ColumnFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.bits_eq`

/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall constants.ColumnFlags.from_bits_retain_eq (bits : U16) :
    constants.ColumnFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.from_bits_retain_eq`

/-- `empty`: no flags. -/
recall constants.ColumnFlags.empty_spec :
    constants.ColumnFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.empty_spec`

/-- `is_empty`: no bit set. -/
recall constants.ColumnFlags.is_empty_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.is_empty_spec`

/-- `is_all`: every known flag set. -/
recall constants.ColumnFlags.is_all_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.is_all self ⦃ b => (b ↔ columnFlagsAll &&& self.val = columnFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.is_all_spec`

/-- `intersects`: a common bit. -/
recall constants.ColumnFlags.intersects_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.intersects_spec`

/-- `contains`: every bit of `other` is in `self`. -/
recall constants.ColumnFlags.contains_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.contains_spec`

/-- `union`: the bits of either. -/
recall constants.ColumnFlags.union_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.union_spec`

/-- `insert`: `union`. -/
recall constants.ColumnFlags.insert_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.insert_spec`

/-- `intersection`: the common bits. -/
recall constants.ColumnFlags.intersection_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.intersection_spec`

/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall constants.ColumnFlags.difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.difference_spec`

/-- `remove`: `difference`. -/
recall constants.ColumnFlags.remove_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.remove_spec`

/-- `symmetric_difference`: the bits in exactly one. -/
recall constants.ColumnFlags.symmetric_difference_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.symmetric_difference_spec`

/-- `toggle`: `symmetric_difference`. -/
recall constants.ColumnFlags.toggle_spec (self other : constants.ColumnFlags) :
    constants.ColumnFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.toggle_spec`

/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall constants.ColumnFlags.set_spec (self other : constants.ColumnFlags) (value : Bool) :
    constants.ColumnFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.set_spec`

/-- `complement`: the known flags not in `self`. -/
recall constants.ColumnFlags.complement_spec (self : constants.ColumnFlags) :
    constants.ColumnFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& columnFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.ColumnFlags.complement_spec`

/-- `From<ColumnFlags>`: the raw value. -/
recall U16.Insts.CoreConvertFromColumnFlags.from_eq (val : constants.ColumnFlags) :
    U16.Insts.CoreConvertFromColumnFlags.from val = ok val

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U16.Insts.CoreConvertFromColumnFlags.from_eq`

/-! ### `struct CursorType and its impls` -/

/-- `bits`: the raw value. -/
recall constants.CursorType.bits_eq (self : constants.CursorType) :
    constants.CursorType.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.CursorType.bits_eq`

/-- `From<CursorType> for u8`: the raw value. -/
recall U8.Insts.CoreConvertFromCursorType.from_eq (val : constants.CursorType) :
    U8.Insts.CoreConvertFromCursorType.from val = ok val

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.CoreConvertFromCursorType.from_eq`

/-! ### `struct StmtExecuteParamsFlags and its impls` -/

/-- `bits`: the raw value. -/
recall constants.StmtExecuteParamsFlags.bits_eq (self : constants.StmtExecuteParamsFlags) :
    constants.StmtExecuteParamsFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StmtExecuteParamsFlags.bits_eq`

/-- `From<StmtExecuteParamsFlags> for u8`: the raw value. -/
recall U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from_eq (val : constants.StmtExecuteParamsFlags) :
    U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from val = ok val

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from_eq`

/-! ### `struct StmtExecuteParamFlags and its impls` -/

/-- `empty`: no flags. -/
recall constants.StmtExecuteParamFlags.empty_spec :
    constants.StmtExecuteParamFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StmtExecuteParamFlags.empty_spec`

/-- `bits`: the raw value. -/
recall constants.StmtExecuteParamFlags.bits_eq (self : constants.StmtExecuteParamFlags) :
    constants.StmtExecuteParamFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms constants.StmtExecuteParamFlags.bits_eq`

end mysql_common
