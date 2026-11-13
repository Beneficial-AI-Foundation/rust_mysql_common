import Defs.Flags
import Defs.Value

/-!
# Binlog foundations: code tables, flag words, packed temporal formats

The numeric codes of the binlog enumerations and flag words, and MySQL's packed formats of the
fractional-second temporal types (`TIME2`, `DATETIME2`, `TIMESTAMP2`), written from the MySQL
server source:

* `libbinlogevents/include/binlog_event.h` (`Log_event_type`, `enum_binlog_checksum_alg`,
  `LOG_EVENT_*_F` event flags, the `Q_*` query-event status variable codes, `Incident`,
  `Intvar_event::Int_event_type`), `rows_event.h` (`Table_map_event::Optional_metadata_field_type`,
  the `*_F` rows-event flags), `control_events.h` (`Gtid_event::FLAG_MAY_HAVE_SBR`,
  `Transaction_payload_event` fields), `compression/base.h` (`type::ZSTD = 0`, `type::NONE = 255`),
  `load_data_events.h` (`enum_load_dup_handling`), `sql/rpl_gtid.h` (`MAX_GNO`), `plugin/semisync` (`kPacketFlagSync = 0x01`), `sql/log_event.h`
  (`User_var_log_event::UNSIGNED_F = 0x01`);
* `mysys/my_time.cc` (`my_time_packed_from_binary`/`my_time_packed_to_binary`,
  `my_datetime_packed_from_binary`/`my_datetime_packed_to_binary`,
  `my_timestamp_from_binary`/`my_timestamp_to_binary`, `TIME_to_longlong_time_packed`,
  `TIME_from_longlong_time_packed`, `TIME_to_longlong_datetime_packed`,
  `TIME_from_longlong_datetime_packed`) and `include/my_time.h` (`MY_PACKED_TIME_*`).

Integers here are mathematical (`Nat`, `Int`): MySQL's C arithmetic on these formats never wraps
for the values they hold, except where a docstring says so.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Byte orders and two's complement -/

/-- The low `k` bytes of the two's-complement representation of `x`, most significant first
    (MySQL's `mi_int<k>store`). -/
def beBytesI (k : Nat) (x : Int) : List U8 := (leBytesI k x).reverse

/-- `x` reduced to a signed 64-bit integer (two's-complement wrap-around). -/
def wrapI64 (x : Int) : Int := toSigned 64 (x % (2 ^ 64 : Int)).toNat

/-! ## Enumeration codes -/

open binlog.consts.BinlogVersion in
/-- The binlog format version number (the `binlog_version` field of the format description event):
    1 (MySQL 3.23), 2 (4.0.0–4.0.1), 3 (4.0.2–4.x), 4 (5.0 and later). -/
def binlogVersionCode : binlog.consts.BinlogVersion → Nat
  | Version1 => 1 | Version2 => 2 | Version3 => 3 | Version4 => 4

open binlog.consts.BinlogVersion in
/-- Every binlog version. -/
def allBinlogVersions : List binlog.consts.BinlogVersion := [Version1, Version2, Version3, Version4]

/-- The binlog version numbered `n`, if any. -/
def binlogVersionOfCode (n : Nat) : Option binlog.consts.BinlogVersion :=
  allBinlogVersions.find? (fun v => binlogVersionCode v = n)

open binlog.consts.EventType in
/-- The event type code (`Log_event_type`, the `type_code` byte of the event header). MySQL's
    names differ in places: `HEARTBEAT_EVENT` is `HEARTBEAT_LOG_EVENT`, `IGNORABLE_EVENT` is
    `IGNORABLE_LOG_EVENT`, `ROWS_QUERY_EVENT` is `ROWS_QUERY_LOG_EVENT`, `GTID_EVENT` is
    `GTID_LOG_EVENT`, `ANONYMOUS_GTID_EVENT` is `ANONYMOUS_GTID_LOG_EVENT`,
    `PREVIOUS_GTIDS_EVENT` is `PREVIOUS_GTIDS_LOG_EVENT`. Code `0x29` is MySQL's
    `HEARTBEAT_LOG_EVENT_V2` (MySQL 8.0.26+), which the crate does not know. `ENUM_END_EVENT`
    (`0x2b`) is MySQL's end marker, not an event type. -/
def eventTypeCode : binlog.consts.EventType → Nat
  | UNKNOWN_EVENT => 0x00 | START_EVENT_V3 => 0x01 | QUERY_EVENT => 0x02 | STOP_EVENT => 0x03
  | ROTATE_EVENT => 0x04 | INTVAR_EVENT => 0x05 | LOAD_EVENT => 0x06 | SLAVE_EVENT => 0x07
  | CREATE_FILE_EVENT => 0x08 | APPEND_BLOCK_EVENT => 0x09 | EXEC_LOAD_EVENT => 0x0a
  | DELETE_FILE_EVENT => 0x0b | NEW_LOAD_EVENT => 0x0c | RAND_EVENT => 0x0d
  | USER_VAR_EVENT => 0x0e | FORMAT_DESCRIPTION_EVENT => 0x0f | XID_EVENT => 0x10
  | BEGIN_LOAD_QUERY_EVENT => 0x11 | EXECUTE_LOAD_QUERY_EVENT => 0x12 | TABLE_MAP_EVENT => 0x13
  | PRE_GA_WRITE_ROWS_EVENT => 0x14 | PRE_GA_UPDATE_ROWS_EVENT => 0x15
  | PRE_GA_DELETE_ROWS_EVENT => 0x16 | WRITE_ROWS_EVENT_V1 => 0x17 | UPDATE_ROWS_EVENT_V1 => 0x18
  | DELETE_ROWS_EVENT_V1 => 0x19 | INCIDENT_EVENT => 0x1a | HEARTBEAT_EVENT => 0x1b
  | IGNORABLE_EVENT => 0x1c | ROWS_QUERY_EVENT => 0x1d | WRITE_ROWS_EVENT => 0x1e
  | UPDATE_ROWS_EVENT => 0x1f | DELETE_ROWS_EVENT => 0x20 | GTID_EVENT => 0x21
  | ANONYMOUS_GTID_EVENT => 0x22 | PREVIOUS_GTIDS_EVENT => 0x23
  | TRANSACTION_CONTEXT_EVENT => 0x24 | VIEW_CHANGE_EVENT => 0x25 | XA_PREPARE_LOG_EVENT => 0x26
  | PARTIAL_UPDATE_ROWS_EVENT => 0x27 | TRANSACTION_PAYLOAD_EVENT => 0x28
  | GTID_TAGGED_LOG_EVENT => 0x2a | ENUM_END_EVENT => 0x2b

open binlog.consts.EventType in
/-- Every event type (not the end marker `ENUM_END_EVENT`). -/
def allEventTypes : List binlog.consts.EventType :=
  [UNKNOWN_EVENT, START_EVENT_V3, QUERY_EVENT, STOP_EVENT, ROTATE_EVENT, INTVAR_EVENT, LOAD_EVENT,
   SLAVE_EVENT, CREATE_FILE_EVENT, APPEND_BLOCK_EVENT, EXEC_LOAD_EVENT, DELETE_FILE_EVENT,
   NEW_LOAD_EVENT, RAND_EVENT, USER_VAR_EVENT, FORMAT_DESCRIPTION_EVENT, XID_EVENT,
   BEGIN_LOAD_QUERY_EVENT, EXECUTE_LOAD_QUERY_EVENT, TABLE_MAP_EVENT, PRE_GA_WRITE_ROWS_EVENT,
   PRE_GA_UPDATE_ROWS_EVENT, PRE_GA_DELETE_ROWS_EVENT, WRITE_ROWS_EVENT_V1, UPDATE_ROWS_EVENT_V1,
   DELETE_ROWS_EVENT_V1, INCIDENT_EVENT, HEARTBEAT_EVENT, IGNORABLE_EVENT, ROWS_QUERY_EVENT,
   WRITE_ROWS_EVENT, UPDATE_ROWS_EVENT, DELETE_ROWS_EVENT, GTID_EVENT, ANONYMOUS_GTID_EVENT,
   PREVIOUS_GTIDS_EVENT, TRANSACTION_CONTEXT_EVENT, VIEW_CHANGE_EVENT, XA_PREPARE_LOG_EVENT,
   PARTIAL_UPDATE_ROWS_EVENT, TRANSACTION_PAYLOAD_EVENT, GTID_TAGGED_LOG_EVENT]

/-- The event type with code `n`, if any (none for `0x29` and `0x2b`–`0xff`). -/
def eventTypeOfCode (n : Nat) : Option binlog.consts.EventType :=
  allEventTypes.find? (fun e => eventTypeCode e = n)

open binlog.consts.BinlogChecksumAlg in
/-- `enum_binlog_checksum_alg`: `BINLOG_CHECKSUM_ALG_OFF = 0`, `BINLOG_CHECKSUM_ALG_CRC32 = 1`
    (MySQL's `BINLOG_CHECKSUM_ALG_UNDEF = 255`, "not yet known", has no crate counterpart). -/
def checksumAlgCode : binlog.consts.BinlogChecksumAlg → Nat
  | BINLOG_CHECKSUM_ALG_OFF => 0 | BINLOG_CHECKSUM_ALG_CRC32 => 1

/-- The checksum algorithm with code `n`, if any. -/
def checksumAlgOfCode (n : Nat) : Option binlog.consts.BinlogChecksumAlg :=
  [binlog.consts.BinlogChecksumAlg.BINLOG_CHECKSUM_ALG_OFF,
   binlog.consts.BinlogChecksumAlg.BINLOG_CHECKSUM_ALG_CRC32].find? (fun a => checksumAlgCode a = n)

open binlog.consts.StatusVarKey in
/-- The query-event status variable codes (`Q_FLAGS2_CODE = 0`, `Q_SQL_MODE_CODE`,
    `Q_CATALOG_CODE`, `Q_AUTO_INCREMENT`, `Q_CHARSET_CODE`, `Q_TIME_ZONE_CODE`,
    `Q_CATALOG_NZ_CODE`, `Q_LC_TIME_NAMES_CODE`, `Q_CHARSET_DATABASE_CODE`,
    `Q_TABLE_MAP_FOR_UPDATE_CODE`, `Q_MASTER_DATA_WRITTEN_CODE`, `Q_INVOKER`,
    `Q_UPDATED_DB_NAMES`, `Q_MICROSECONDS`, `Q_COMMIT_TS`, `Q_COMMIT_TS2`,
    `Q_EXPLICIT_DEFAULTS_FOR_TIMESTAMP`, `Q_DDL_LOGGED_WITH_XID`,
    `Q_DEFAULT_COLLATION_FOR_UTF8MB4`, `Q_SQL_REQUIRE_PRIMARY_KEY`,
    `Q_DEFAULT_TABLE_ENCRYPTION = 20`). -/
def statusVarKeyCode : binlog.consts.StatusVarKey → Nat
  | Flags2 => 0 | SqlMode => 1 | Catalog => 2 | AutoIncrement => 3 | Charset => 4 | TimeZone => 5
  | CatalogNz => 6 | LcTimeNames => 7 | CharsetDatabase => 8 | TableMapForUpdate => 9
  | MasterDataWritten => 10 | Invoker => 11 | UpdatedDbNames => 12 | Microseconds => 13
  | CommitTs => 14 | CommitTs2 => 15 | ExplicitDefaultsForTimestamp => 16 | DdlLoggedWithXid => 17
  | DefaultCollationForUtf8mb4 => 18 | SqlRequirePrimaryKey => 19 | DefaultTableEncryption => 20

open binlog.consts.StatusVarKey in
/-- Every status variable key. -/
def allStatusVarKeys : List binlog.consts.StatusVarKey :=
  [Flags2, SqlMode, Catalog, AutoIncrement, Charset, TimeZone, CatalogNz, LcTimeNames,
   CharsetDatabase, TableMapForUpdate, MasterDataWritten, Invoker, UpdatedDbNames, Microseconds,
   CommitTs, CommitTs2, ExplicitDefaultsForTimestamp, DdlLoggedWithXid,
   DefaultCollationForUtf8mb4, SqlRequirePrimaryKey, DefaultTableEncryption]

/-- The status variable key with code `n`, if any (codes 0–20). -/
def statusVarKeyOfCode (n : Nat) : Option binlog.consts.StatusVarKey :=
  allStatusVarKeys.find? (fun k => statusVarKeyCode k = n)

open binlog.consts.LoadDuplicateHandling in
/-- How `LOAD DATA` handles duplicates (`enum_load_dup_handling`): `LOAD_DUP_ERROR = 0`,
    `LOAD_DUP_IGNORE = 1`, `LOAD_DUP_REPLACE = 2`. -/
def loadDupCode : binlog.consts.LoadDuplicateHandling → Nat
  | LOAD_DUP_ERROR => 0 | LOAD_DUP_IGNORE => 1 | LOAD_DUP_REPLACE => 2

open binlog.consts.LoadDuplicateHandling in
/-- The duplicate handling with code `n`, if any. -/
def loadDupOfCode (n : Nat) : Option binlog.consts.LoadDuplicateHandling :=
  [LOAD_DUP_ERROR, LOAD_DUP_IGNORE, LOAD_DUP_REPLACE].find? (fun d => loadDupCode d = n)

open binlog.consts.OptionalMetadataFieldType in
/-- `Table_map_event::Optional_metadata_field_type`: `SIGNEDNESS = 1` up to
    `VECTOR_DIMENSIONALITY = 13`, in declaration order. -/
def optMetaFieldCode : binlog.consts.OptionalMetadataFieldType → Nat
  | SIGNEDNESS => 1 | DEFAULT_CHARSET => 2 | COLUMN_CHARSET => 3 | COLUMN_NAME => 4
  | SET_STR_VALUE => 5 | ENUM_STR_VALUE => 6 | GEOMETRY_TYPE => 7 | SIMPLE_PRIMARY_KEY => 8
  | PRIMARY_KEY_WITH_PREFIX => 9 | ENUM_AND_SET_DEFAULT_CHARSET => 10
  | ENUM_AND_SET_COLUMN_CHARSET => 11 | COLUMN_VISIBILITY => 12 | VECTOR_DIMENSIONALITY => 13

open binlog.consts.OptionalMetadataFieldType in
/-- The optional metadata field type with code `n`, if any (codes 1–13). -/
def optMetaFieldOfCode (n : Nat) : Option binlog.consts.OptionalMetadataFieldType :=
  [SIGNEDNESS, DEFAULT_CHARSET, COLUMN_CHARSET, COLUMN_NAME, SET_STR_VALUE, ENUM_STR_VALUE,
   GEOMETRY_TYPE, SIMPLE_PRIMARY_KEY, PRIMARY_KEY_WITH_PREFIX, ENUM_AND_SET_DEFAULT_CHARSET,
   ENUM_AND_SET_COLUMN_CHARSET, COLUMN_VISIBILITY, VECTOR_DIMENSIONALITY].find?
    (fun f => optMetaFieldCode f = n)

open binlog.consts.IncidentType in
/-- `Incident_event::enum_incident`: `INCIDENT_NONE = 0`, `INCIDENT_LOST_EVENTS = 1`. -/
def incidentTypeCode : binlog.consts.IncidentType → Nat
  | INCIDENT_NONE => 0 | INCIDENT_LOST_EVENTS => 1

open binlog.consts.IncidentType in
/-- The incident type with code `n`, if any. -/
def incidentTypeOfCode (n : Nat) : Option binlog.consts.IncidentType :=
  [INCIDENT_NONE, INCIDENT_LOST_EVENTS].find? (fun t => incidentTypeCode t = n)

open binlog.consts.IntvarEventType in
/-- `Intvar_event::Int_event_type`: `INVALID_INT_EVENT = 0`, `LAST_INSERT_ID_EVENT = 1`,
    `INSERT_ID_EVENT = 2`. -/
def intvarTypeCode : binlog.consts.IntvarEventType → Nat
  | INVALID_INT_EVENT => 0 | LAST_INSERT_ID_EVENT => 1 | INSERT_ID_EVENT => 2

open binlog.consts.IntvarEventType in
/-- The intvar event type with code `n`, if any. -/
def intvarTypeOfCode (n : Nat) : Option binlog.consts.IntvarEventType :=
  [INVALID_INT_EVENT, LAST_INSERT_ID_EVENT, INSERT_ID_EVENT].find? (fun t => intvarTypeCode t = n)

open binlog.consts.TransactionPayloadFields in
/-- The `Transaction_payload_event` header field codes: `OTW_PAYLOAD_HEADER_END_MARK = 0`,
    `OTW_PAYLOAD_SIZE_FIELD = 1`, `OTW_PAYLOAD_COMPRESSION_TYPE_FIELD = 2`,
    `OTW_PAYLOAD_UNCOMPRESSED_SIZE_FIELD = 3`. -/
def txPayloadFieldCode : binlog.consts.TransactionPayloadFields → Nat
  | OTW_PAYLOAD_HEADER_END_MARK => 0 | OTW_PAYLOAD_SIZE_FIELD => 1
  | OTW_PAYLOAD_COMPRESSION_TYPE_FIELD => 2 | OTW_PAYLOAD_UNCOMPRESSED_SIZE_FIELD => 3

open binlog.consts.TransactionPayloadFields in
/-- The payload field with code `n`, if any. -/
def txPayloadFieldOfCode (n : Nat) : Option binlog.consts.TransactionPayloadFields :=
  [OTW_PAYLOAD_HEADER_END_MARK, OTW_PAYLOAD_SIZE_FIELD, OTW_PAYLOAD_COMPRESSION_TYPE_FIELD,
   OTW_PAYLOAD_UNCOMPRESSED_SIZE_FIELD].find? (fun f => txPayloadFieldCode f = n)

open binlog.consts.TransactionPayloadCompressionType in
/-- The payload compression type codes (`mysql::binlog::event::compression::type`): `ZSTD = 0`,
    `NONE = 255`. -/
def txCompressionCode : binlog.consts.TransactionPayloadCompressionType → Nat
  | ZSTD => 0 | NONE => 255

open binlog.consts.TransactionPayloadCompressionType in
/-- The compression type with code `n`, if any. -/
def txCompressionOfCode (n : Nat) : Option binlog.consts.TransactionPayloadCompressionType :=
  [ZSTD, NONE].find? (fun c => txCompressionCode c = n)

/-- `binlog_row_value_options` bits: `PARTIAL_JSON_UPDATES = 1` (the crate's
    `BinlogRowValueOptions` is a one-variant enum, not a flag word: only the exact value 1 is
    accepted). -/
def rowValueOptionsOfCode (n : Nat) : Option binlog.row.BinlogRowValueOptions :=
  if n = 1 then some .PARTIAL_JSON_UPDATES else none

/-! ## Flag words (all bits the crate names) -/

/-- The event header flags (`LOG_EVENT_*_F`, `u16`): `BINLOG_IN_USE` (0x1), `FORCED_ROTATE` (0x2),
    `THREAD_SPECIFIC` (0x4), `SUPPRESS_USE` (0x8), `UPDATE_TABLE_MAP_VERSION` (0x10),
    `ARTIFICIAL` (0x20), `RELAY_LOG` (0x40), `IGNORABLE` (0x80), `NO_FILTER` (0x100),
    `MTS_ISOLATE` (0x200). -/
def eventFlagsAll : Nat := 0x3FF

/-- The semi-sync flags (`u8`): `SEMI_SYNC_ACK_REQ` (0x1). -/
def semiSyncFlagsAll : Nat := 0x1

/-- The GTID event flags (`u8`): `MAY_HAVE_SBR` (0x1). -/
def gtidFlagsAll : Nat := 0x1

/-- The rows event flags (`u16`): `STMT_END` (0x1), `NO_FOREIGN_KEY_CHECKS` (0x2),
    `RELAXED_UNIQUE_CHECKS` (0x4), `COMPLETE_ROWS` (0x8). -/
def rowsEventFlagsAll : Nat := 0xF

/-- The user variable flags (`u8`): `UNSIGNED` (0x1). -/
def userVarFlagsAll : Nat := 0x1

/-! ## GTID group numbers -/

/-- `MAX_GNO` = `INT64_MAX` (the crate's `Gno::MAX_GNO`). In MySQL 8.0 this is `GNO_END`
    (`sql/rpl_gtid.h`), documented as *one past* the largest group number: `parse_gno` rejects
    `gno >= GNO_END` (`rpl_gtid_set.cc`), so the valid group numbers are `[1, maxGno)`. -/
def maxGno : Nat := 2 ^ 63 - 1

/-! ## Packed temporal values (`include/my_time.h`, `mysys/my_time.cc`)

MySQL represents a TIME or DATETIME in memory as a *packed* signed 64-bit integer: the integer part
(the fields, bit-packed) shifted left by 24 bits, plus the microseconds. -/

/-- `MY_PACKED_TIME_GET_INT_PART(x)` = `x >> 24`, an arithmetic shift (rounds towards −∞). -/
def packedIntPart (x : Int) : Int := Int.fdiv x (2 ^ 24)

/-- `MY_PACKED_TIME_GET_FRAC_PART(x)` = `x % (1 << 24)`, C's remainder (the sign of `x`). -/
def packedFracPart (x : Int) : Int := Int.tmod x (2 ^ 24)

/-- `MY_PACKED_TIME_MAKE(i, f)` = `(i << 24) + f` (for the integer parts below, `i << 24` never
    leaves the 64-bit range, so this is exact). -/
def packedMake (i f : Int) : Int := i * 2 ^ 24 + f

/-- `TIME_to_longlong_time_packed`: `hms = ((days * 24 + hours) << 12) | (minutes << 6) | seconds`
    (written `+`: the fields are in range), then `MY_PACKED_TIME_MAKE(hms, micros)`, negated for a
    negative time. -/
def timePack (neg : Bool) (days hours minutes seconds micros : Nat) : Int :=
  let hms : Nat := (days * 24 + hours) * 2 ^ 12 + minutes * 2 ^ 6 + seconds
  let t := packedMake hms micros
  if neg then -t else t

/-- `TIME_from_longlong_time_packed`, into the crate's TIME value: the sign, then from the absolute
    value: hours = bits 12–21 of the integer part, minutes = bits 6–11, seconds = bits 0–5,
    microseconds = the fraction. MySQL's `MYSQL_TIME` keeps all the hours in `hour` (up to 1023);
    the crate's `Value::Time` splits them into days and hours (`hours / 24`, `hours % 24`). -/
def timeFromPacked (p : Int) : Val :=
  let a : Nat := p.natAbs
  let hms := a / 2 ^ 24
  let h := hms / 2 ^ 12 % 2 ^ 10
  .time (decide (p < 0)) (h / 24) (h % 24) (hms / 2 ^ 6 % 2 ^ 6) (hms % 2 ^ 6) (a % 2 ^ 24)

/-- `TIME_to_longlong_datetime_packed`: `ymd = ((year * 13 + month) << 5) | day`,
    `hms = (hour << 12) | (minute << 6) | second` (written `+`), then
    `MY_PACKED_TIME_MAKE((ymd << 17) | hms, micros)`. -/
def datetimePack (year month day hour minute second micros : Nat) : Int :=
  let ymd : Nat := (year * 13 + month) * 2 ^ 5 + day
  let hms : Nat := hour * 2 ^ 12 + minute * 2 ^ 6 + second
  packedMake (ymd * 2 ^ 17 + hms) micros

/-- `TIME_from_longlong_datetime_packed`, into the crate's DATE value, from the absolute value of
    `p`: `ymdhms` = the integer part, `ymd = ymdhms >> 17`, `ym = ymd >> 5`; day = `ymd % 32`,
    month = `ym % 13`, year = `ym / 13`; `hms = ymdhms % 2^17`: second = `hms % 64`,
    minute = `(hms >> 6) % 64`, hour = `hms >> 12`; microseconds = the fraction. MySQL also
    records the sign (`neg`), which the crate's `Value::Date` has no room for (a DATETIME is never
    negative). -/
def datetimeFromPacked (p : Int) : Val :=
  let a : Nat := p.natAbs
  let ymdhms := a / 2 ^ 24
  let ymd := ymdhms / 2 ^ 17
  let ym := ymd / 2 ^ 5
  let hms := ymdhms % 2 ^ 17
  .date (ym / 13) (ym % 13) (ymd % 2 ^ 5) (hms / 2 ^ 12) (hms / 2 ^ 6 % 2 ^ 6) (hms % 2 ^ 6)
    (a % 2 ^ 24)

/-! ## The binary (on-disk / binlog) formats -/

/-- The number of bytes of the fractional part for `dec` fractional digits (`dec` is the column's
    metadata byte): 1 (`dec` 1, 2), 2 (3, 4), 3 (5, 6), none otherwise (`dec = 0`; MySQL's readers
    treat `dec > 6` like 0, in their `default:` branches). -/
def fracBytes (dec : Nat) : Nat :=
  if dec = 1 ∨ dec = 2 then 1 else if dec = 3 ∨ dec = 4 then 2 else if dec = 5 ∨ dec = 6 then 3
  else 0

/-- The unit in microseconds of the stored fraction: 10000 (`dec` 1, 2), 100 (3, 4), 1 (5, 6),
    and `10^6` (no fraction) otherwise. A fraction `us` is representable iff `us < 10^6` and
    `fracUnit dec ∣ us`. -/
def fracUnit (dec : Nat) : Nat :=
  if dec = 1 ∨ dec = 2 then 10000 else if dec = 3 ∨ dec = 4 then 100
  else if dec = 5 ∨ dec = 6 then 1 else 1000000

/-- `my_time_packed_from_binary`: TIME2 is 3 big-endian bytes of `intpart + 0x800000` followed by
    `fracBytes dec` bytes of fraction. For `dec` 1–4 the fraction is unsigned (in units of
    `fracUnit dec`); a negative time with a non-zero fraction stores the integer part rounded down
    and the fraction as `0x100 - |frac|` (resp. `0x10000 - |frac|`), and the reader undoes it
    (`intpart++; frac -= 0x100`). For `dec` 5, 6 the whole 6 bytes are `packed + 0x800000000000`.
    `none` if there are fewer than `3 + fracBytes dec` bytes; otherwise the packed value and the
    rest. -/
def time2Read (dec : Nat) (bs : List U8) : Option (Int × List U8) :=
  if bs.length < 3 + fracBytes dec then none else
  let ip : Int := (beNat (bs.take 3) : Int) - 0x800000
  let p : Int :=
    if dec = 1 ∨ dec = 2 then
      let fr : Int := (beNat ((bs.drop 3).take 1) : Int)
      if ip < 0 ∧ fr ≠ 0 then packedMake (ip + 1) ((fr - 0x100) * 10000)
      else packedMake ip (fr * 10000)
    else if dec = 3 ∨ dec = 4 then
      let fr : Int := (beNat ((bs.drop 3).take 2) : Int)
      if ip < 0 ∧ fr ≠ 0 then packedMake (ip + 1) ((fr - 0x10000) * 100)
      else packedMake ip (fr * 100)
    else if dec = 5 ∨ dec = 6 then (beNat (bs.take 6) : Int) - 0x800000000000
    else packedMake ip 0
  some (p, bs.drop (3 + fracBytes dec))

/-- `my_time_packed_to_binary`: the inverse of `time2Read`: `mi_int3store(intpart + 0x800000)`,
    then the fraction divided by its unit (C division, so it carries the sign of a negative time)
    as a 1- or 2-byte two's-complement number; for `dec` 5, 6, `mi_int6store(p + 0x800000000000)`. -/
def time2Bin (dec : Nat) (p : Int) : List U8 :=
  let ip := beBytesI 3 (packedIntPart p + 0x800000)
  if dec = 1 ∨ dec = 2 then ip ++ beBytesI 1 (Int.tdiv (packedFracPart p) 10000)
  else if dec = 3 ∨ dec = 4 then ip ++ beBytesI 2 (Int.tdiv (packedFracPart p) 100)
  else if dec = 5 ∨ dec = 6 then beBytesI 6 (p + 0x800000000000)
  else ip

/-- The TIME2 input on which the crate's reader for 1–2 fractional digits computes
    `frac -= 0x100` in `u32` (MySQL: `int`): a negative integer part (first 3 bytes below
    `0x800000`) with a non-zero fraction byte. Every negative TIME(1)/TIME(2) value with a non-zero
    fraction is stored this way (e.g. `-00:00:00.5`). -/
def time2NegFracBug (dec : Nat) (bs : List U8) : Prop :=
  (dec = 1 ∨ dec = 2) ∧ 4 ≤ bs.length ∧ beNat (bs.take 3) < 0x800000 ∧
    beNat ((bs.drop 3).take 1) ≠ 0

/-- The signed fraction of DATETIME2/TIMESTAMP2 (`fb` = the `fracBytes dec` fraction bytes), in
    microseconds: `(signed char) * 10000` (`dec` 1, 2), `mi_sint2korr * 100` (3, 4),
    `mi_sint3korr` (5, 6), 0 otherwise. -/
def temporalFracRead (dec : Nat) (fb : List U8) : Int :=
  if dec = 1 ∨ dec = 2 then toSigned 8 (beNat fb) * 10000
  else if dec = 3 ∨ dec = 4 then toSigned 16 (beNat fb) * 100
  else if dec = 5 ∨ dec = 6 then toSigned 24 (beNat fb)
  else 0

/-- `my_datetime_packed_from_binary`: DATETIME2 is 5 big-endian bytes of
    `intpart + 0x8000000000`, then the fraction (`temporalFracRead`); the packed value is
    `MY_PACKED_TIME_MAKE(intpart, frac)`. `none` if there are fewer than `5 + fracBytes dec` bytes. -/
def datetime2Read (dec : Nat) (bs : List U8) : Option (Int × List U8) :=
  if bs.length < 5 + fracBytes dec then none else
  let ip : Int := (beNat (bs.take 5) : Int) - 0x8000000000
  some (packedMake ip (temporalFracRead dec ((bs.drop 5).take (fracBytes dec))),
    bs.drop (5 + fracBytes dec))

/-- The fraction bytes MySQL's `*_to_binary` writers store for a fraction `f` (microseconds, C
    division by the unit): 1, 2 or 3 two's-complement bytes. -/
def temporalFracBin (dec : Nat) (f : Int) : List U8 :=
  if dec = 1 ∨ dec = 2 then beBytesI 1 (Int.tdiv f 10000)
  else if dec = 3 ∨ dec = 4 then beBytesI 2 (Int.tdiv f 100)
  else if dec = 5 ∨ dec = 6 then beBytesI 3 f
  else []

/-- `my_datetime_packed_to_binary`: `mi_int5store(intpart + 0x8000000000)`, then the fraction. -/
def datetime2Bin (dec : Nat) (p : Int) : List U8 :=
  beBytesI 5 (packedIntPart p + 0x8000000000) ++ temporalFracBin dec (packedFracPart p)

/-- The crate's TIMESTAMP2 reader: 4 big-endian bytes of seconds since the epoch, then the
    fraction (`temporalFracRead`); `none` if there are fewer than `4 + fracBytes dec` bytes.
    **Differences from MySQL's `my_timestamp_from_binary`** (only on data MySQL never writes): MySQL
    reads the seconds unsigned (`mi_uint4korr`), the crate as an `i32` (values from `2^31`, past
    the TIMESTAMP range's end in 2038, come out negative); for `dec` 1, 2 MySQL reads the fraction
    byte unsigned (`(int)ptr[4]`), the crate signed (bytes from 128, i.e. fractions MySQL never
    writes, come out negative). -/
def timestamp2Read (dec : Nat) (bs : List U8) : Option ((Int × Int) × List U8) :=
  if bs.length < 4 + fracBytes dec then none else
  some ((toSigned 32 (beNat (bs.take 4)), temporalFracRead dec ((bs.drop 4).take (fracBytes dec))),
    bs.drop (4 + fracBytes dec))

/-- `my_timestamp_to_binary`: `mi_int4store(sec)`, then the fraction. -/
def timestamp2Bin (dec : Nat) (sec : Nat) (usec : Nat) : List U8 :=
  beBytes 4 sec ++ temporalFracBin dec usec

end Defs
