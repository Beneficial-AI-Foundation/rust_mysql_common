import Proofs.Defs.LemmasBinlogCore

/-!
# Facts about the binlog foundation definitions (`formal/specs/Defs/BinlogCore.lean`, `formal/specs/Defs/BinlogValue.lean`)
    Pure-Lean properties a signer should read: each code table is inverted by its `ofCode`;
    MySQL's packed TIME/DATETIME conversions and binary TIME2/DATETIME2/TIMESTAMP2 formats are
    inverse to each other on their ranges; the STRING metadata MySQL writes decodes to the
    column's length; the intended binlog value reader inverts the encoder; and the bug predicate
    `time2NegFracBug` holds exactly on MySQL's encodings of negative TIME(1)/TIME(2) values with
    a fraction. Proofs: `Proofs/Defs/LemmasBinlogCore.lean`.

    **Trusted axioms:** none.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

open constants.ColumnType

/-! ### Lemmas -/

/-- `binlogVersionOfCode` inverts `binlogVersionCode`. -/
recall binlogVersionOfCode_binlogVersionCode (x : binlog.consts.BinlogVersion) :
    binlogVersionOfCode (binlogVersionCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.binlogVersionOfCode_binlogVersionCode
/-- `eventTypeOfCode` inverts `eventTypeCode` (every event type but the end marker). -/
recall eventTypeOfCode_eventTypeCode (x : binlog.consts.EventType) (h : x ≠ .ENUM_END_EVENT) :
    eventTypeOfCode (eventTypeCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.eventTypeOfCode_eventTypeCode
/-- `checksumAlgOfCode` inverts `checksumAlgCode`. -/
recall checksumAlgOfCode_checksumAlgCode (x : binlog.consts.BinlogChecksumAlg) :
    checksumAlgOfCode (checksumAlgCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.checksumAlgOfCode_checksumAlgCode
/-- `statusVarKeyOfCode` inverts `statusVarKeyCode`. -/
recall statusVarKeyOfCode_statusVarKeyCode (x : binlog.consts.StatusVarKey) :
    statusVarKeyOfCode (statusVarKeyCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.statusVarKeyOfCode_statusVarKeyCode
/-- `loadDupOfCode` inverts `loadDupCode`. -/
recall loadDupOfCode_loadDupCode (x : binlog.consts.LoadDuplicateHandling) :
    loadDupOfCode (loadDupCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.loadDupOfCode_loadDupCode
/-- `optMetaFieldOfCode` inverts `optMetaFieldCode`. -/
recall optMetaFieldOfCode_optMetaFieldCode (x : binlog.consts.OptionalMetadataFieldType) :
    optMetaFieldOfCode (optMetaFieldCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.optMetaFieldOfCode_optMetaFieldCode
/-- `incidentTypeOfCode` inverts `incidentTypeCode`. -/
recall incidentTypeOfCode_incidentTypeCode (x : binlog.consts.IncidentType) :
    incidentTypeOfCode (incidentTypeCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.incidentTypeOfCode_incidentTypeCode
/-- `intvarTypeOfCode` inverts `intvarTypeCode`. -/
recall intvarTypeOfCode_intvarTypeCode (x : binlog.consts.IntvarEventType) :
    intvarTypeOfCode (intvarTypeCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.intvarTypeOfCode_intvarTypeCode
/-- `txPayloadFieldOfCode` inverts `txPayloadFieldCode`. -/
recall txPayloadFieldOfCode_txPayloadFieldCode (x : binlog.consts.TransactionPayloadFields) :
    txPayloadFieldOfCode (txPayloadFieldCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.txPayloadFieldOfCode_txPayloadFieldCode
/-- `txCompressionOfCode` inverts `txCompressionCode`. -/
recall txCompressionOfCode_txCompressionCode (x : binlog.consts.TransactionPayloadCompressionType) :
    txCompressionOfCode (txCompressionCode x) = some x

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.txCompressionOfCode_txCompressionCode
/-- `ofCode` gives a value with that code (so the codes of distinct values differ, and `TryFrom` returns the value with exactly the given code). -/
recall eventTypeCode_eventTypeOfCode (n : Nat) (x : binlog.consts.EventType) (h : eventTypeOfCode n = some x) :
    eventTypeCode x = n

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.eventTypeCode_eventTypeOfCode
/-- MySQL 8.0.26+'s `HEARTBEAT_LOG_EVENT_V2` (`0x29`) is not a crate event type. -/
recall eventTypeOfCode_heartbeat_v2 :
    eventTypeOfCode 0x29 = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.eventTypeOfCode_heartbeat_v2
/-- MySQL's packed TIME (`TIME_to_longlong_time_packed`) unpacks back (`TIME_from_longlong_time_packed`) to the time, for fields in range (up to 1023 hours) and not a negative zero. -/
recall timeFromPacked_timePack (neg : Bool) (d h m s us : Nat)
    (hr : h < 24 ∧ m < 60 ∧ s < 60 ∧ d * 24 + h < 1024 ∧ us < 2 ^ 24)
    (hz : ¬(neg = true ∧ d = 0 ∧ h = 0 ∧ m = 0 ∧ s = 0 ∧ us = 0)) :
    timeFromPacked (timePack neg d h m s us) = .time neg d h m s us

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.timeFromPacked_timePack
/-- MySQL's packed DATETIME unpacks back to the datetime, for fields in range. -/
recall datetimeFromPacked_datetimePack (y mo d h mi s us : Nat)
    (hr : y ≤ 9999 ∧ mo ≤ 12 ∧ d < 32 ∧ h < 24 ∧ mi < 60 ∧ s < 60 ∧ us < 2 ^ 24) :
    datetimeFromPacked (datetimePack y mo d h mi s us) = .date y mo d h mi s us

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.datetimeFromPacked_datetimePack
/-- MySQL's TIME2 reader inverts its writer, on packed values in range with a representable fraction (including negative values with a fraction at 1–2 digits, which the crate's reader crashes on). -/
recall time2Read_time2Bin (dec : Nat) (p : Int) (tail : List U8) (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2Read dec (time2Bin dec p ++ tail) = some (p, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.time2Read_time2Bin
/-- MySQL's DATETIME2 reader inverts its writer, on non-negative packed values below `2^63` with a representable fraction. -/
recall datetime2Read_datetime2Bin (dec : Nat) (p : Int) (tail : List U8) (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ packedFracPart p < 10 ^ 6) :
    datetime2Read dec (datetime2Bin dec p ++ tail) = some (p, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.datetime2Read_datetime2Bin
/-- The TIMESTAMP2 reader inverts MySQL's writer, on timestamps in range with a representable fraction. -/
recall timestamp2Read_timestamp2Bin (dec sec usec : Nat) (tail : List U8) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec = 0) :
    timestamp2Read dec (timestamp2Bin dec sec usec ++ tail) = some (((sec : Int), (usec : Int)), tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.timestamp2Read_timestamp2Bin
/-- The crate's TIME2 bug condition holds exactly on MySQL's encodings of negative values with a fraction, at 1–2 fractional digits. -/
recall time2NegFracBug_time2Bin (dec : Nat) (p : Int) (tail : List U8) (hd : dec = 1 ∨ dec = 2)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2NegFracBug dec (time2Bin dec p ++ tail) ↔ p < 0 ∧ packedFracPart p ≠ 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.time2NegFracBug_time2Bin
/-- MySQL's TIME(1) encoding of `-00:00:00.5`: `7F FF FF CE`. -/
recall time2Bin_neg_half :
    time2Bin 1 (timePack true 0 0 0 0 500000) = [byte 0x7F, byte 0xFF, byte 0xFF, byte 0xCE]

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.time2Bin_neg_half
/-- The STRING metadata MySQL writes for a column of `L < 1024` bytes (real type `STRING`, `0xFE`) decodes to `L`. -/
recall stringFieldLen_mysql (L : Nat) (hL : L < 1024) :
    stringFieldLen (0xFE ^^^ ((L &&& 0x300) >>> 4)) (L % 256) = L

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.stringFieldLen_mysql
/-- The intended reader inverts the encoder: `binlogRead` reads back `binlogEnc` (bugs included: `binlogRead` is MySQL's reading). -/
recall binlogRead_binlogEnc (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) :
    binlogRead ct md uns (bs ++ tail) = .ok v tail

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.binlogRead_binlogEnc
/-- The bug inputs are those of the encoded bug values: an encoded value outside `binlogEncBug` is not a `binlogBug` input (so `deserialize_roundtrip` follows from `deserialize_ok` and `binlogRead_binlogEnc`). -/
recall not_binlogBug_of_binlogEnc (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) (hb : ¬ binlogEncBug ct md uns v) :
    ¬ binlogBug ct md uns (bs ++ tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.not_binlogBug_of_binlogEnc
end Defs
