import Defs
import Proofs.Util.BinlogValue

/-! Sanity lemmas about `Defs/BinlogCore.lean` and `Defs/BinlogValue.lean` (recalled in
`Specs/DefsBinlogCore.lean`). Helper lemmas: `Proofs/Util/BinlogValue.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common

namespace Defs

open constants.ColumnType

/-- `binlogVersionOfCode` inverts `binlogVersionCode`. -/
theorem binlogVersionOfCode_binlogVersionCode (x : binlog.consts.BinlogVersion) :
    binlogVersionOfCode (binlogVersionCode x) = some x := by
  cases x <;> rfl

/-- `eventTypeOfCode` inverts `eventTypeCode` (every event type but the end marker). -/
theorem eventTypeOfCode_eventTypeCode (x : binlog.consts.EventType) (h : x ≠ .ENUM_END_EVENT) :
    eventTypeOfCode (eventTypeCode x) = some x := by
  cases x <;> first | rfl | exact absurd rfl h

/-- `checksumAlgOfCode` inverts `checksumAlgCode`. -/
theorem checksumAlgOfCode_checksumAlgCode (x : binlog.consts.BinlogChecksumAlg) :
    checksumAlgOfCode (checksumAlgCode x) = some x := by
  cases x <;> rfl

/-- `statusVarKeyOfCode` inverts `statusVarKeyCode`. -/
theorem statusVarKeyOfCode_statusVarKeyCode (x : binlog.consts.StatusVarKey) :
    statusVarKeyOfCode (statusVarKeyCode x) = some x := by
  cases x <;> rfl

/-- `loadDupOfCode` inverts `loadDupCode`. -/
theorem loadDupOfCode_loadDupCode (x : binlog.consts.LoadDuplicateHandling) :
    loadDupOfCode (loadDupCode x) = some x := by
  cases x <;> rfl

/-- `optMetaFieldOfCode` inverts `optMetaFieldCode`. -/
theorem optMetaFieldOfCode_optMetaFieldCode (x : binlog.consts.OptionalMetadataFieldType) :
    optMetaFieldOfCode (optMetaFieldCode x) = some x := by
  cases x <;> rfl

/-- `incidentTypeOfCode` inverts `incidentTypeCode`. -/
theorem incidentTypeOfCode_incidentTypeCode (x : binlog.consts.IncidentType) :
    incidentTypeOfCode (incidentTypeCode x) = some x := by
  cases x <;> rfl

/-- `intvarTypeOfCode` inverts `intvarTypeCode`. -/
theorem intvarTypeOfCode_intvarTypeCode (x : binlog.consts.IntvarEventType) :
    intvarTypeOfCode (intvarTypeCode x) = some x := by
  cases x <;> rfl

/-- `txPayloadFieldOfCode` inverts `txPayloadFieldCode`. -/
theorem txPayloadFieldOfCode_txPayloadFieldCode (x : binlog.consts.TransactionPayloadFields) :
    txPayloadFieldOfCode (txPayloadFieldCode x) = some x := by
  cases x <;> rfl

/-- `txCompressionOfCode` inverts `txCompressionCode`. -/
theorem txCompressionOfCode_txCompressionCode (x : binlog.consts.TransactionPayloadCompressionType) :
    txCompressionOfCode (txCompressionCode x) = some x := by
  cases x <;> rfl

/-- `ofCode` gives a value with that code (so the codes of distinct values differ, and `TryFrom` returns the value with exactly the given code). -/
theorem eventTypeCode_eventTypeOfCode (n : Nat) (x : binlog.consts.EventType) (h : eventTypeOfCode n = some x) :
    eventTypeCode x = n := by
  unfold eventTypeOfCode at h
  have := List.find?_some h
  simpa using this

/-- MySQL 8.0.26+'s `HEARTBEAT_LOG_EVENT_V2` (`0x29`) is not a crate event type. -/
theorem eventTypeOfCode_heartbeat_v2 :
    eventTypeOfCode 0x29 = none := by
  rfl

/-- MySQL's packed TIME (`TIME_to_longlong_time_packed`) unpacks back (`TIME_from_longlong_time_packed`) to the time, for fields in range (up to 1023 hours) and not a negative zero. -/
theorem timeFromPacked_timePack (neg : Bool) (d h m s us : Nat)
    (hr : h < 24 ∧ m < 60 ∧ s < 60 ∧ d * 24 + h < 1024 ∧ us < 2 ^ 24)
    (hz : ¬(neg = true ∧ d = 0 ∧ h = 0 ∧ m = 0 ∧ s = 0 ∧ us = 0)) :
    timeFromPacked (timePack neg d h m s us) = .time neg d h m s us := 
  timeFromPacked_timePack' neg d h m s us hr hz

/-- MySQL's packed DATETIME unpacks back to the datetime, for fields in range. -/
theorem datetimeFromPacked_datetimePack (y mo d h mi s us : Nat)
    (hr : y ≤ 9999 ∧ mo ≤ 12 ∧ d < 32 ∧ h < 24 ∧ mi < 60 ∧ s < 60 ∧ us < 2 ^ 24) :
    datetimeFromPacked (datetimePack y mo d h mi s us) = .date y mo d h mi s us := 
  datetimeFromPacked_datetimePack' y mo d h mi s us hr

/-- MySQL's TIME2 reader inverts its writer, on packed values in range with a representable fraction (including negative values with a fraction at 1–2 digits, which the crate's reader crashes on). -/
theorem time2Read_time2Bin (dec : Nat) (p : Int) (tail : List U8) (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2Read dec (time2Bin dec p ++ tail) = some (p, tail) := 
  time2Read_time2Bin' dec p tail hp hf

/-- MySQL's DATETIME2 reader inverts its writer, on non-negative packed values below `2^63` with a representable fraction. -/
theorem datetime2Read_datetime2Bin (dec : Nat) (p : Int) (tail : List U8) (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ packedFracPart p < 10 ^ 6) :
    datetime2Read dec (datetime2Bin dec p ++ tail) = some (p, tail) := 
  datetime2Read_datetime2Bin' dec p tail hp hf

/-- The TIMESTAMP2 reader inverts MySQL's writer, on timestamps in range with a representable fraction. -/
theorem timestamp2Read_timestamp2Bin (dec sec usec : Nat) (tail : List U8) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec = 0) :
    timestamp2Read dec (timestamp2Bin dec sec usec ++ tail) = some (((sec : Int), (usec : Int)), tail) := 
  timestamp2Read_timestamp2Bin' dec sec usec tail hs hu

/-- The crate's TIME2 bug condition holds exactly on MySQL's encodings of negative values with a fraction, at 1–2 fractional digits. -/
theorem time2NegFracBug_time2Bin (dec : Nat) (p : Int) (tail : List U8) (hd : dec = 1 ∨ dec = 2)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2NegFracBug dec (time2Bin dec p ++ tail) ↔ p < 0 ∧ packedFracPart p ≠ 0 := 
  time2NegFracBug_time2Bin' dec p tail hd hp hf

/-- MySQL's TIME(1) encoding of `-00:00:00.5`: `7F FF FF CE`. -/
theorem time2Bin_neg_half :
    time2Bin 1 (timePack true 0 0 0 0 500000) = [byte 0x7F, byte 0xFF, byte 0xFF, byte 0xCE] := by
  decide

/-- The STRING metadata MySQL writes for a column of `L < 1024` bytes (real type `STRING`, `0xFE`) decodes to `L`. -/
theorem stringFieldLen_mysql (L : Nat) (hL : L < 1024) :
    stringFieldLen (0xFE ^^^ ((L &&& 0x300) >>> 4)) (L % 256) = L := by
  revert L
  set_option maxRecDepth 100000 in decide

/-- The intended reader inverts the encoder: `binlogRead` reads back `binlogEnc` (bugs included: `binlogRead` is MySQL's reading). -/
theorem binlogRead_binlogEnc (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) :
    binlogRead ct md uns (bs ++ tail) = .ok v tail := 
  binlogRead_binlogEnc' ct md uns v bs tail h

/-- The bug inputs are those of the encoded bug values: an encoded value outside `binlogEncBug` is not a `binlogBug` input (so `deserialize_roundtrip` follows from `deserialize_ok` and `binlogRead_binlogEnc`). -/
theorem not_binlogBug_of_binlogEnc (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) (hb : ¬ binlogEncBug ct md uns v) :
    ¬ binlogBug ct md uns (bs ++ tail) := 
  not_binlogBug_of_binlogEnc' ct md uns v bs tail h hb

end Defs
