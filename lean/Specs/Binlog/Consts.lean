import Proofs.Binlog.Consts.BinlogVersion
import Proofs.Binlog.Consts.EventType
import Proofs.Binlog.Consts.EventFlags
import Proofs.Binlog.Consts.BinlogChecksumAlg
import Proofs.Binlog.Consts.StatusVarKey
import Proofs.Binlog.Consts.SemiSyncFlags
import Proofs.Binlog.Consts.LoadDuplicateHandling
import Proofs.Binlog.Consts.OptionalMetadataFieldType
import Proofs.Binlog.Consts.IncidentType
import Proofs.Binlog.Consts.IntvarEventType
import Proofs.Binlog.Consts.GtidFlags
import Proofs.Binlog.Consts.Gno
import Proofs.Binlog.Consts.RowsEventFlags
import Proofs.Binlog.Consts.UserVarFlags
import Proofs.Binlog.Consts.TransactionPayloadFields
import Proofs.Binlog.Consts.TransactionPayloadCompressionType

/-!
# `src/binlog/consts.rs`
    The binlog enumerations (`TryFrom` from their wire codes, `From` to them) and the plain flag
    words (`EventFlags`, `SemiSyncFlags`, `GtidFlags`, `RowsEventFlags`, `UserVarFlags`), checked
    against MySQL's code tables (`Defs/BinlogCore.lean`).

    **Patch.** The flag types are plain `#[repr(transparent)]` structs with the `bitflags` 2.13 API
    written out (translation patch 142, as patch 20 for `constants.rs`); Aeneas models each as its
    raw integer. The statements are about the patched code.

    **Configuration.** As in `Specs/Binlog/Mod.lean`.

    **Definitions used.** `Defs/BinlogCore.lean` (`binlogVersionCode`/`binlogVersionOfCode`,
    `eventTypeOfCode`, `checksumAlgOfCode`, `statusVarKeyOfCode`, `loadDupCode`/`loadDupOfCode`,
    `optMetaFieldOfCode`, `incidentTypeOfCode`, `intvarTypeCode`/`intvarTypeOfCode`,
    `txPayloadFieldOfCode`, `txCompressionOfCode`, `eventFlagsAll`, `semiSyncFlagsAll`,
    `gtidFlagsAll`, `rowsEventFlagsAll`, `userVarFlagsAll`, `maxGno`), `Defs/Flags.lean`
    (`andNot`, `complementBits`), `Defs/Bytes.lean` (`byte`).

    **Trusted axioms.** None. (The `TryFrom<u64>` impls call `u8::try_from(u64)`, modelled exactly
    in `FunsExternal.lean`; `Result::unwrap` is the Aeneas library's.)

    **Not covered.** The named flag constants (plain definitions), derived `Clone`/`Copy`/
    `PartialEq`/`Eq`/`Hash`, `Debug`/`Display` (opaque), the flag iterators/`from_name` and the
    formatting impls (excluded in Cargo.toml), `From<Unknown*> for u8/u16` (not translated:
    unused), `From<TransactionPayloadFields> for u8/u64`, `From<IncidentType> for u16` (not
    translated: unused).

    **Behaviour to note.**
    * `EventType::try_from` rejects `0x29` (MySQL 8.0.26+'s `HEARTBEAT_LOG_EVENT_V2`) as unknown.
    * `TryFrom<u64> for TransactionPayloadFields` and `for TransactionPayloadCompressionType`
      **panic** on an unknown value of 256 or more (`x.try_into().unwrap()` into the `u8` error
      payload); these values come from the wire (`TransactionPayloadEvent` header fields).
    * `Gno::try_from` accepts `0` and `[MIN_GNO, MAX_GNO)`: `MAX_GNO` itself is rejected, although
      the type's doc and the error's message say the range is `[MIN_GNO, MAX_GNO]`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum BinlogVersion and its impls` -/

/-- `From<BinlogVersion> for u16`: the version number. -/
recall U16.Insts.CoreConvertFromBinlogVersion.from_spec (x : binlog.consts.BinlogVersion) :
    U16.Insts.CoreConvertFromBinlogVersion.from x ⦃ r => r.val = binlogVersionCode x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U16.Insts.CoreConvertFromBinlogVersion.from_spec`
/-- `TryFrom<u16> for BinlogVersion`: total; the version with that number (1–4), or the number back as the error. -/
recall binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from_spec (value : U16) :
    binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from value =
      ok (match binlogVersionOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from_spec`
/-! ### `enum EventType and its impls` -/

/-- `TryFrom<u8> for EventType`: total; the event type with that code (`Log_event_type`), or the byte back as the error. Unknown: `0x29` (MySQL's `HEARTBEAT_LOG_EVENT_V2`) and `0x2b`–`0xff` (in particular `ENUM_END_EVENT`, MySQL's end marker, is never returned). -/
recall binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec (value : U8) :
    binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from value =
      ok (match eventTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec`
/-! ### `struct EventFlags and its impls` -/

/-- `all`: every flag the crate names (`eventFlagsAll`). -/
recall binlog.consts.EventFlags.all_spec :
    binlog.consts.EventFlags.all ⦃ r => r.val = eventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.all_spec`
/-- `from_bits_truncate`: the known bits of `bits`. -/
recall binlog.consts.EventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& eventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.from_bits_truncate_spec`
/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall binlog.consts.EventFlags.from_bits_spec (bits : U16) :
    binlog.consts.EventFlags.from_bits bits ⦃ r => r = if bits.val &&& eventFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.from_bits_spec`
/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from_spec (val : U16) :
    binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from val ⦃ r =>
      r = if val.val &&& eventFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.Insts.CoreConvertTryFromU16UnknownEventFlags.try_from_spec`
/-- `bits`: the raw value. -/
recall binlog.consts.EventFlags.bits_eq (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.bits_eq`
/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall binlog.consts.EventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.EventFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.from_bits_retain_eq`
/-- `empty`: no flags. -/
recall binlog.consts.EventFlags.empty_spec :
    binlog.consts.EventFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.empty_spec`
/-- `is_empty`: no bit set. -/
recall binlog.consts.EventFlags.is_empty_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.is_empty_spec`
/-- `is_all`: every known flag set. -/
recall binlog.consts.EventFlags.is_all_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.is_all self ⦃ b => (b ↔ eventFlagsAll &&& self.val = eventFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.is_all_spec`
/-- `intersects`: a common bit. -/
recall binlog.consts.EventFlags.intersects_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.intersects_spec`
/-- `contains`: every bit of `other` is in `self`. -/
recall binlog.consts.EventFlags.contains_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.contains_spec`
/-- `union`: the bits of either. -/
recall binlog.consts.EventFlags.union_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.union_spec`
/-- `insert`: `union`. -/
recall binlog.consts.EventFlags.insert_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.insert_spec`
/-- `intersection`: the common bits. -/
recall binlog.consts.EventFlags.intersection_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.intersection_spec`
/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall binlog.consts.EventFlags.difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.difference_spec`
/-- `remove`: `difference`. -/
recall binlog.consts.EventFlags.remove_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.remove_spec`
/-- `symmetric_difference`: the bits in exactly one. -/
recall binlog.consts.EventFlags.symmetric_difference_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.symmetric_difference_spec`
/-- `toggle`: `symmetric_difference`. -/
recall binlog.consts.EventFlags.toggle_spec (self other : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.toggle_spec`
/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall binlog.consts.EventFlags.set_spec (self other : binlog.consts.EventFlags) (value : Bool) :
    binlog.consts.EventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.set_spec`
/-- `complement`: the known flags not in `self`. -/
recall binlog.consts.EventFlags.complement_spec (self : binlog.consts.EventFlags) :
    binlog.consts.EventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& eventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.EventFlags.complement_spec`
/-! ### `enum BinlogChecksumAlg and its impls` -/

/-- `TryFrom<u8> for BinlogChecksumAlg`: total; `OFF` (0), `CRC32` (1), else the byte back as the error (also MySQL's `BINLOG_CHECKSUM_ALG_UNDEF`, 255). -/
recall binlog.consts.BinlogChecksumAlg.Insts.CoreConvertTryFromU8UnknownChecksumAlg.try_from_spec (value : U8) :
    binlog.consts.BinlogChecksumAlg.Insts.CoreConvertTryFromU8UnknownChecksumAlg.try_from value =
      ok (match checksumAlgOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.BinlogChecksumAlg.Insts.CoreConvertTryFromU8UnknownChecksumAlg.try_from_spec`
/-! ### `enum StatusVarKey and its impls` -/

/-- `TryFrom<u8> for StatusVarKey`: total; the query-event status variable with that code (MySQL's `Q_*` codes 0–20), or the byte back as the error. -/
recall binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from_spec (value : U8) :
    binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from value =
      ok (match statusVarKeyOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from_spec`
/-! ### `struct SemiSyncFlags and its impls` -/

/-- `all`: every flag the crate names (`semiSyncFlagsAll`). -/
recall binlog.consts.SemiSyncFlags.all_spec :
    binlog.consts.SemiSyncFlags.all ⦃ r => r.val = semiSyncFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.all_spec`
/-- `from_bits_truncate`: the known bits of `bits`. -/
recall binlog.consts.SemiSyncFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& semiSyncFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.from_bits_truncate_spec`
/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall binlog.consts.SemiSyncFlags.from_bits_spec (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits bits ⦃ r => r = if bits.val &&& semiSyncFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.from_bits_spec`
/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from_spec (val : U8) :
    binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from val ⦃ r =>
      r = if val.val &&& semiSyncFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.Insts.CoreConvertTryFromU8UnknownSemiSyncFlags.try_from_spec`
/-- `bits`: the raw value. -/
recall binlog.consts.SemiSyncFlags.bits_eq (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.bits_eq`
/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall binlog.consts.SemiSyncFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.SemiSyncFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.from_bits_retain_eq`
/-- `empty`: no flags. -/
recall binlog.consts.SemiSyncFlags.empty_spec :
    binlog.consts.SemiSyncFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.empty_spec`
/-- `is_empty`: no bit set. -/
recall binlog.consts.SemiSyncFlags.is_empty_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.is_empty_spec`
/-- `is_all`: every known flag set. -/
recall binlog.consts.SemiSyncFlags.is_all_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.is_all self ⦃ b => (b ↔ semiSyncFlagsAll &&& self.val = semiSyncFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.is_all_spec`
/-- `intersects`: a common bit. -/
recall binlog.consts.SemiSyncFlags.intersects_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.intersects_spec`
/-- `contains`: every bit of `other` is in `self`. -/
recall binlog.consts.SemiSyncFlags.contains_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.contains_spec`
/-- `union`: the bits of either. -/
recall binlog.consts.SemiSyncFlags.union_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.union_spec`
/-- `insert`: `union`. -/
recall binlog.consts.SemiSyncFlags.insert_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.insert_spec`
/-- `intersection`: the common bits. -/
recall binlog.consts.SemiSyncFlags.intersection_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.intersection_spec`
/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall binlog.consts.SemiSyncFlags.difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.difference_spec`
/-- `remove`: `difference`. -/
recall binlog.consts.SemiSyncFlags.remove_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.remove_spec`
/-- `symmetric_difference`: the bits in exactly one. -/
recall binlog.consts.SemiSyncFlags.symmetric_difference_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.symmetric_difference_spec`
/-- `toggle`: `symmetric_difference`. -/
recall binlog.consts.SemiSyncFlags.toggle_spec (self other : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.toggle_spec`
/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall binlog.consts.SemiSyncFlags.set_spec (self other : binlog.consts.SemiSyncFlags) (value : Bool) :
    binlog.consts.SemiSyncFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.set_spec`
/-- `complement`: the known flags not in `self`. -/
recall binlog.consts.SemiSyncFlags.complement_spec (self : binlog.consts.SemiSyncFlags) :
    binlog.consts.SemiSyncFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& semiSyncFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.SemiSyncFlags.complement_spec`
/-! ### `enum LoadDuplicateHandling and its impls` -/

/-- `From<LoadDuplicateHandling> for u8`: the code. -/
recall U8.Insts.CoreConvertFromLoadDuplicateHandling.from_spec (x : binlog.consts.LoadDuplicateHandling) :
    U8.Insts.CoreConvertFromLoadDuplicateHandling.from x ⦃ r => r.val = loadDupCode x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.CoreConvertFromLoadDuplicateHandling.from_spec`
/-- `TryFrom<u8> for LoadDuplicateHandling`: total; the handling with that code (0–2), or the byte back as the error. -/
recall binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from_spec (value : U8) :
    binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from value =
      ok (match loadDupOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from_spec`
/-! ### `enum OptionalMetadataFieldType and its impls` -/

/-- `TryFrom<u8> for OptionalMetadataFieldType`: total; the field type with that code (1–13), or the byte back as the error. -/
recall binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from_spec (value : U8) :
    binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from value =
      ok (match optMetaFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from_spec`
/-! ### `enum IncidentType and its impls` -/

/-- `TryFrom<u16> for IncidentType`: total; `INCIDENT_NONE` (0), `INCIDENT_LOST_EVENTS` (1), else the number back as the error. -/
recall binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from_spec (value : U16) :
    binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from value =
      ok (match incidentTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from_spec`
/-! ### `enum IntvarEventType and its impls` -/

/-- `From<IntvarEventType> for u8`: the code. -/
recall U8.Insts.CoreConvertFromIntvarEventType.from_spec (x : binlog.consts.IntvarEventType) :
    U8.Insts.CoreConvertFromIntvarEventType.from x ⦃ r => r.val = intvarTypeCode x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.CoreConvertFromIntvarEventType.from_spec`
/-- `TryFrom<u8> for IntvarEventType`: total; the type with that code (0–2), or the byte back as the error. -/
recall binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from_spec (value : U8) :
    binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from value =
      ok (match intvarTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from_spec`
/-! ### `struct GtidFlags and its impls` -/

/-- `all`: every flag the crate names (`gtidFlagsAll`). -/
recall binlog.consts.GtidFlags.all_spec :
    binlog.consts.GtidFlags.all ⦃ r => r.val = gtidFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.all_spec`
/-- `from_bits_truncate`: the known bits of `bits`. -/
recall binlog.consts.GtidFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& gtidFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.from_bits_truncate_spec`
/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall binlog.consts.GtidFlags.from_bits_spec (bits : U8) :
    binlog.consts.GtidFlags.from_bits bits ⦃ r => r = if bits.val &&& gtidFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.from_bits_spec`
/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from_spec (val : U8) :
    binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from val ⦃ r =>
      r = if val.val &&& gtidFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.Insts.CoreConvertTryFromU8UnknownGtidFlags.try_from_spec`
/-- `bits`: the raw value. -/
recall binlog.consts.GtidFlags.bits_eq (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.bits_eq`
/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall binlog.consts.GtidFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.GtidFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.from_bits_retain_eq`
/-- `empty`: no flags. -/
recall binlog.consts.GtidFlags.empty_spec :
    binlog.consts.GtidFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.empty_spec`
/-- `Default`: no flags. -/
recall binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default_spec :
    binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.Insts.CoreDefaultDefault.default_spec`
/-- `is_empty`: no bit set. -/
recall binlog.consts.GtidFlags.is_empty_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.is_empty_spec`
/-- `is_all`: every known flag set. -/
recall binlog.consts.GtidFlags.is_all_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.is_all self ⦃ b => (b ↔ gtidFlagsAll &&& self.val = gtidFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.is_all_spec`
/-- `intersects`: a common bit. -/
recall binlog.consts.GtidFlags.intersects_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.intersects_spec`
/-- `contains`: every bit of `other` is in `self`. -/
recall binlog.consts.GtidFlags.contains_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.contains_spec`
/-- `union`: the bits of either. -/
recall binlog.consts.GtidFlags.union_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.union_spec`
/-- `insert`: `union`. -/
recall binlog.consts.GtidFlags.insert_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.insert_spec`
/-- `intersection`: the common bits. -/
recall binlog.consts.GtidFlags.intersection_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.intersection_spec`
/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall binlog.consts.GtidFlags.difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.difference_spec`
/-- `remove`: `difference`. -/
recall binlog.consts.GtidFlags.remove_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.remove_spec`
/-- `symmetric_difference`: the bits in exactly one. -/
recall binlog.consts.GtidFlags.symmetric_difference_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.symmetric_difference_spec`
/-- `toggle`: `symmetric_difference`. -/
recall binlog.consts.GtidFlags.toggle_spec (self other : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.toggle_spec`
/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall binlog.consts.GtidFlags.set_spec (self other : binlog.consts.GtidFlags) (value : Bool) :
    binlog.consts.GtidFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.set_spec`
/-- `complement`: the known flags not in `self`. -/
recall binlog.consts.GtidFlags.complement_spec (self : binlog.consts.GtidFlags) :
    binlog.consts.GtidFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& gtidFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.GtidFlags.complement_spec`
/-! ### `struct Gno and its impls` -/

/-- `Gno::MAX_GNO`: `i64::MAX` (`Defs.maxGno`, MySQL's `MAX_GNO`). -/
recall binlog.consts.Gno.MAX_GNO_eq :
    binlog.consts.Gno.MAX_GNO = ok ⟨BitVec.ofNat 64 maxGno⟩

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.Gno.MAX_GNO_eq`
/-- `TryFrom<u64> for Gno`: total; `Ok` for `0` (the anonymous GTID's number) and for `MIN_GNO ≤ value < MAX_GNO`, else the value back as the error. **Quirk**: `MAX_GNO` itself is rejected, while the type's documentation and the error message ("out of range [MIN_GNO, MAX_GNO]") say it is in range. -/
recall binlog.consts.Gno.Insts.CoreConvertTryFromU64InvalidGno.try_from_spec (value : U64) :
    binlog.consts.Gno.Insts.CoreConvertTryFromU64InvalidGno.try_from value =
      ok (if value.val = 0 ∨ (1 ≤ value.val ∧ value.val < maxGno) then .Ok value else .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.Gno.Insts.CoreConvertTryFromU64InvalidGno.try_from_spec`
/-! ### `struct RowsEventFlags and its impls` -/

/-- `all`: every flag the crate names (`rowsEventFlagsAll`). -/
recall binlog.consts.RowsEventFlags.all_spec :
    binlog.consts.RowsEventFlags.all ⦃ r => r.val = rowsEventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.all_spec`
/-- `from_bits_truncate`: the known bits of `bits`. -/
recall binlog.consts.RowsEventFlags.from_bits_truncate_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& rowsEventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.from_bits_truncate_spec`
/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall binlog.consts.RowsEventFlags.from_bits_spec (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits bits ⦃ r => r = if bits.val &&& rowsEventFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.from_bits_spec`
/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from_spec (val : U16) :
    binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from val ⦃ r =>
      r = if val.val &&& rowsEventFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.Insts.CoreConvertTryFromU16UnknownRowsEventFlags.try_from_spec`
/-- `bits`: the raw value. -/
recall binlog.consts.RowsEventFlags.bits_eq (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.bits_eq`
/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall binlog.consts.RowsEventFlags.from_bits_retain_eq (bits : U16) :
    binlog.consts.RowsEventFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.from_bits_retain_eq`
/-- `empty`: no flags. -/
recall binlog.consts.RowsEventFlags.empty_spec :
    binlog.consts.RowsEventFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.empty_spec`
/-- `is_empty`: no bit set. -/
recall binlog.consts.RowsEventFlags.is_empty_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.is_empty_spec`
/-- `is_all`: every known flag set. -/
recall binlog.consts.RowsEventFlags.is_all_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.is_all self ⦃ b => (b ↔ rowsEventFlagsAll &&& self.val = rowsEventFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.is_all_spec`
/-- `intersects`: a common bit. -/
recall binlog.consts.RowsEventFlags.intersects_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.intersects_spec`
/-- `contains`: every bit of `other` is in `self`. -/
recall binlog.consts.RowsEventFlags.contains_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.contains_spec`
/-- `union`: the bits of either. -/
recall binlog.consts.RowsEventFlags.union_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.union_spec`
/-- `insert`: `union`. -/
recall binlog.consts.RowsEventFlags.insert_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.insert_spec`
/-- `intersection`: the common bits. -/
recall binlog.consts.RowsEventFlags.intersection_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.intersection_spec`
/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall binlog.consts.RowsEventFlags.difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.difference self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.difference_spec`
/-- `remove`: `difference`. -/
recall binlog.consts.RowsEventFlags.remove_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.remove self other ⦃ r => r.val = andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.remove_spec`
/-- `symmetric_difference`: the bits in exactly one. -/
recall binlog.consts.RowsEventFlags.symmetric_difference_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.symmetric_difference_spec`
/-- `toggle`: `symmetric_difference`. -/
recall binlog.consts.RowsEventFlags.toggle_spec (self other : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.toggle_spec`
/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall binlog.consts.RowsEventFlags.set_spec (self other : binlog.consts.RowsEventFlags) (value : Bool) :
    binlog.consts.RowsEventFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 16 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.set_spec`
/-- `complement`: the known flags not in `self`. -/
recall binlog.consts.RowsEventFlags.complement_spec (self : binlog.consts.RowsEventFlags) :
    binlog.consts.RowsEventFlags.complement self ⦃ r => r.val = complementBits 16 self.val &&& rowsEventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.RowsEventFlags.complement_spec`
/-! ### `struct UserVarFlags and its impls` -/

/-- `all`: every flag the crate names (`userVarFlagsAll`). -/
recall binlog.consts.UserVarFlags.all_spec :
    binlog.consts.UserVarFlags.all ⦃ r => r.val = userVarFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.all_spec`
/-- `from_bits_truncate`: the known bits of `bits`. -/
recall binlog.consts.UserVarFlags.from_bits_truncate_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_truncate bits ⦃ r => r.val = bits.val &&& userVarFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.from_bits_truncate_spec`
/-- `from_bits`: `Some(bits)` if every bit is known, else `None`. -/
recall binlog.consts.UserVarFlags.from_bits_spec (bits : U8) :
    binlog.consts.UserVarFlags.from_bits bits ⦃ r => r = if bits.val &&& userVarFlagsAll = bits.val then some bits else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.from_bits_spec`
/-- `TryFrom`: `from_bits`, with the raw value as the error. -/
recall binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from_spec (val : U8) :
    binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from val ⦃ r =>
      r = if val.val &&& userVarFlagsAll = val.val then .Ok val else .Err val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.Insts.CoreConvertTryFromU8UnknownUserVarFlags.try_from_spec`
/-- `bits`: the raw value. -/
recall binlog.consts.UserVarFlags.bits_eq (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.bits self = ok self

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.bits_eq`
/-- `from_bits_retain`: the raw value, unknown bits kept. -/
recall binlog.consts.UserVarFlags.from_bits_retain_eq (bits : U8) :
    binlog.consts.UserVarFlags.from_bits_retain bits = ok bits

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.from_bits_retain_eq`
/-- `empty`: no flags. -/
recall binlog.consts.UserVarFlags.empty_spec :
    binlog.consts.UserVarFlags.empty ⦃ r => r.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.empty_spec`
/-- `is_empty`: no bit set. -/
recall binlog.consts.UserVarFlags.is_empty_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_empty self ⦃ b => (b ↔ self.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.is_empty_spec`
/-- `is_all`: every known flag set. -/
recall binlog.consts.UserVarFlags.is_all_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.is_all self ⦃ b => (b ↔ userVarFlagsAll &&& self.val = userVarFlagsAll) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.is_all_spec`
/-- `intersects`: a common bit. -/
recall binlog.consts.UserVarFlags.intersects_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersects self other ⦃ b => (b ↔ self.val &&& other.val ≠ 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.intersects_spec`
/-- `contains`: every bit of `other` is in `self`. -/
recall binlog.consts.UserVarFlags.contains_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.contains self other ⦃ b => (b ↔ self.val &&& other.val = other.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.contains_spec`
/-- `union`: the bits of either. -/
recall binlog.consts.UserVarFlags.union_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.union self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.union_spec`
/-- `insert`: `union`. -/
recall binlog.consts.UserVarFlags.insert_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.insert self other ⦃ r => r.val = self.val ||| other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.insert_spec`
/-- `intersection`: the common bits. -/
recall binlog.consts.UserVarFlags.intersection_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.intersection self other ⦃ r => r.val = self.val &&& other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.intersection_spec`
/-- `difference`: the bits of `self` not in `other` (unknown bits of `self` kept). -/
recall binlog.consts.UserVarFlags.difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.difference self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.difference_spec`
/-- `remove`: `difference`. -/
recall binlog.consts.UserVarFlags.remove_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.remove self other ⦃ r => r.val = andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.remove_spec`
/-- `symmetric_difference`: the bits in exactly one. -/
recall binlog.consts.UserVarFlags.symmetric_difference_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.symmetric_difference self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.symmetric_difference_spec`
/-- `toggle`: `symmetric_difference`. -/
recall binlog.consts.UserVarFlags.toggle_spec (self other : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.toggle self other ⦃ r => r.val = self.val ^^^ other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.toggle_spec`
/-- `set(other, value)`: `insert` if `value`, else `remove`. -/
recall binlog.consts.UserVarFlags.set_spec (self other : binlog.consts.UserVarFlags) (value : Bool) :
    binlog.consts.UserVarFlags.set self other value ⦃ r =>
      r.val = if value then self.val ||| other.val else andNot 8 self.val other.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.set_spec`
/-- `complement`: the known flags not in `self`. -/
recall binlog.consts.UserVarFlags.complement_spec (self : binlog.consts.UserVarFlags) :
    binlog.consts.UserVarFlags.complement self ⦃ r => r.val = complementBits 8 self.val &&& userVarFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.UserVarFlags.complement_spec`
/-! ### `enum TransactionPayloadFields and its impls` -/

/-- `TryFrom<u8> for TransactionPayloadFields`: total; the header field with that code, or the byte back as the error. -/
recall binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU8UnknownTransactionPayloadFields.try_from_spec (value : U8) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU8UnknownTransactionPayloadFields.try_from value =
      ok (match txPayloadFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU8UnknownTransactionPayloadFields.try_from_spec`
/-- `TryFrom<u64> for TransactionPayloadFields`, for values below 256: the header field with that code, or the value (as a byte) back as the error. -/
recall binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_spec (value : U64) (h : value.val < 256) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from value =
      ok (match txPayloadFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err (byte value.val))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_spec`
/-- **Crash path.** `TryFrom<u64> for TransactionPayloadFields` panics on every value of 256 or more: the error payload is a `u8`, built with `x.try_into().unwrap()`. The value is read from the wire (a `TransactionPayloadEvent` header field), so a malformed event crashes the reader. -/
recall binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_panics (value : U64) (h : 256 ≤ value.val) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from value = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_panics`
/-! ### `enum TransactionPayloadCompressionType and its impls` -/

/-- `TryFrom<u8> for TransactionPayloadCompressionType`: total; the compression type (`ZSTD` = 0, `NONE` = 255) with that code, or the byte back as the error. -/
recall binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU8UnknownTransactionPayloadCompressionType.try_from_spec (value : U8) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU8UnknownTransactionPayloadCompressionType.try_from value =
      ok (match txCompressionOfCode value.val with
        | some x => .Ok x
        | none => .Err value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU8UnknownTransactionPayloadCompressionType.try_from_spec`
/-- `TryFrom<u64> for TransactionPayloadCompressionType`, for values below 256: the compression type (`ZSTD` = 0, `NONE` = 255) with that code, or the value (as a byte) back as the error. -/
recall binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_spec (value : U64) (h : value.val < 256) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from value =
      ok (match txCompressionOfCode value.val with
        | some x => .Ok x
        | none => .Err (byte value.val))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_spec`
/-- **Crash path.** `TryFrom<u64> for TransactionPayloadCompressionType` panics on every value of 256 or more: the error payload is a `u8`, built with `x.try_into().unwrap()`. The value is read from the wire (a `TransactionPayloadEvent` header field), so a malformed event crashes the reader. -/
recall binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_panics (value : U64) (h : 256 ≤ value.val) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from value = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_panics`
end mysql_common
