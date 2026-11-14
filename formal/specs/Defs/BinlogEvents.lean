import Defs.Connection
import Defs.VarLen
import Defs.Flags
import Defs.BinlogCore

/-!
# Binlog events (`src/binlog/events`)

From the MySQL source documentation of the binary log format (libbinlogevents,
<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_replication_binlog_event.html>
and the class pages of `binary_log::*_event`). All integers are little-endian.

* **Common header** (19 bytes, binlog v4): `timestamp` (4), `type_code` (1), `server_id` (4),
  `event_size` (4), `log_pos` (4), `flags` (2). The event data (post-header and body) follows; with
  checksums enabled, the event ends with a 4-byte CRC32; a `FORMAT_DESCRIPTION_EVENT` written by a
  checksum-capable server (≥ 5.6.1) ends with the checksum algorithm (1) and the checksum (4).
* **Post-header lengths** are announced per event type in the `FORMAT_DESCRIPTION_EVENT`
  (`post_header_len[type - 1]`). Readers skip what they do not know.
* `FORMAT_DESCRIPTION_EVENT`: `binlog_version` (2), `server_version` (50, `0`-padded),
  `create_timestamp` (4), `header_length` (1, `19`), `post_header_len` (one byte per type).
* `QUERY_EVENT`: post-header `thread_id` (4), `query_exec_time` (4), `db_len` (1), `error_code`
  (2), `status_vars_len` (2) (13 bytes; more if the FDE says so); body: `status_vars`, `db`
  (`db_len` bytes), `0x00`, `query` (rest).
* Status variables: a key byte and a value whose length depends on the key (`Q_FLAGS2_CODE` 4,
  `Q_SQL_MODE_CODE` 8, `Q_CATALOG_CODE` length + bytes + `0x00`, `Q_AUTO_INCREMENT` 4,
  `Q_CHARSET_CODE` 6, `Q_TIME_ZONE_CODE` / `Q_CATALOG_NZ_CODE` length + bytes, `Q_LC_TIME_NAMES_CODE`
  2, `Q_CHARSET_DATABASE_CODE` 2, `Q_TABLE_MAP_FOR_UPDATE_CODE` 8, `Q_MASTER_DATA_WRITTEN_CODE` 4,
  `Q_INVOKER` user and host each length + bytes, `Q_UPDATED_DB_NAMES` count + that many
  `0`-terminated names (none if the count is 254, `OVER_MAX_DBS_IN_EVENT_MTS`), `Q_MICROSECONDS` 3,
  `Q_COMMIT_TS` / `Q_COMMIT_TS2` 0, `Q_EXPLICIT_DEFAULTS_FOR_TIMESTAMP` 1, `Q_DDL_LOGGED_WITH_XID` 8,
  `Q_DEFAULT_COLLATION_FOR_UTF8MB4` 2, `Q_SQL_REQUIRE_PRIMARY_KEY` 1,
  `Q_DEFAULT_TABLE_ENCRYPTION` 1).
* `ROTATE_EVENT`: `position` (8), `new_log_ident` (rest). `INTVAR_EVENT`: `type` (1), `val` (8).
  `RAND_EVENT`: `seed1` (8), `seed2` (8). `XID_EVENT`: `xid` (8) after the post-header.
  `INCIDENT_EVENT`: `type` (2), message as a 1-byte length and bytes. `ROWS_QUERY_LOG_EVENT`: a
  length byte (ignored: the query can be longer) and the query (rest). `BEGIN_LOAD_QUERY_EVENT`:
  `file_id` (4), block (rest). `EXECUTE_LOAD_QUERY_EVENT`: the query post-header, `file_id` (4),
  `start_pos` (4), `end_pos` (4), `dup_handling` (1), then as `QUERY_EVENT`.
* `GTID_LOG_EVENT` / `ANONYMOUS_GTID_LOG_EVENT`: `gtid_flags` (1), `sid` (16), `gno` (8),
  then optionally `lt_type` (1, `2`), `last_committed` (8), `sequence_number` (8),
  `immediate_commit_timestamp` (7; bit 55 set iff `original_commit_timestamp` (7) follows),
  `transaction_length` (lenenc), `immediate_server_version` (4; bit 31 set iff
  `original_server_version` (4) follows). Absent server versions are `UNDEFINED_SERVER_VERSION`
  (999999).
* `PREVIOUS_GTIDS_LOG_EVENT`: `n_sids` (8; in the tagged format byte 7 is the format, `1`, bits
  8..55 the count), then per SID: `uuid` (16), (tagged: the tag as a varlen length and bytes),
  `n_intervals` (8), and per interval `start` (8), `end` (8).
* `TABLE_MAP_EVENT`: post-header `table_id` (6; 4 if the post-header is 6 bytes), `flags` (2);
  body: database name (1-byte length, bytes, `0x00`), table name (same), `column_count`
  (lenenc), `column_type` (`column_count` bytes), the metadata block (lenenc length and
  bytes), the NULL bitmap (`(column_count + 7) / 8` bytes), optional metadata (rest, TLV).
* Rows events (`WRITE/UPDATE/DELETE_ROWS_EVENT` v1 and v2, `PARTIAL_UPDATE_ROWS_EVENT`):
  post-header `table_id` (6; 4 if the post-header is 6 bytes), `flags` (2), and in v2 the
  `extra_row_info` length (2, counting itself) and data; body `width` (lenenc), the
  columns-present bitmaps (one for write and delete, two for update), rows (rest).
* `TRANSACTION_PAYLOAD_EVENT`: a header of fields (lenenc type, lenenc length, lenenc value):
  compression type (2), uncompressed size (3, only when compressed), payload size (1), then the
  end mark (0) and the payload.

The readers below describe the crate's parsers; their docstrings say where they deviate from
the format. The encoders are the layouts as the crate fills them from its fields.

**Shared definitions.** The codes of the binlog enums and the flag masks (`eventTypeCode`,
`eventTypeOfCode`, `allEventTypes`, `statusVarKeyCode`, `binlogVersionCode`, `checksumAlgCode`,
`intvarTypeCode`, `incidentTypeCode`, `loadDupCode`, `txCompressionCode`, `eventFlagsAll`,
`rowsEventFlagsAll`, `gtidFlagsAll`, …) are those of `Defs/BinlogCore.lean`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Reading results -/

/-- `r, rest` is what a reader with specification `spec` returns: if `spec` reads a value `v`
    leaving `tail`, then `Ok` with `view` equal to `v` and `rest = tail`; if `spec` fails, an
    error (what the reader leaves of the buffer then is not stated). -/
def ReadsAs {T V : Type} (view : T → V) (spec : Option (V × List U8))
    (r : core.result.Result T core.io.error.Error) (rest : io.ParseBuf) : Prop :=
  match spec with
  | some (v, tail) => (okPart r).map view = some v ∧ rest.val = tail
  | none => okPart r = none

/-- An `(Option, rest)` reader result as an optional pair. -/
def optFst {A : Type} : Option A × List U8 → Option (A × List U8)
  | (some a, r) => some (a, r)
  | (none, _) => none

/-- `k` bytes from the front of `bs`, or `none` if there are fewer. -/
def takeExact (k : Nat) (bs : List U8) : Option (List U8 × List U8) :=
  if k ≤ bs.length then some (bs.take k, bs.drop k) else none

/-- A string with a 1-byte length (`U8Bytes`), as the crate writes it: truncated to 255 bytes. -/
def u8Str (s : List U8) : List U8 := byte (min s.length 255) :: s.take 255

/-- `s` as a fixed-length text of `L` bytes (`FixedLengthText<L>`): truncated or `0`-padded. -/
def fixedText (L : Nat) (s : List U8) : List U8 := s.take L ++ List.replicate (L - min L s.length) (byte 0)

/-- The cap of every `BinlogStruct::len` of the crate: `u32::MAX - 19` (the largest event data
    that fits an event of at most `u32::MAX` bytes). -/
def evLenCap : Nat := 2 ^ 32 - 1 - 19

/-! ## Rows-event kinds -/

/-- The rows-event kinds: v2 events carry `extra_row_info` (codes 30, 31, 32, 39). -/
def rowsIsV2 (t : binlog.consts.EventType) : Bool := eventTypeCode t ∈ [30, 31, 32, 39]

/-- Update events carry two column bitmaps (codes 24, 31, 39). -/
def rowsIsUpdate (t : binlog.consts.EventType) : Bool := eventTypeCode t ∈ [24, 31, 39]

/-- Delete events carry only the before-image bitmap (codes 25, 32). -/
def rowsIsDelete (t : binlog.consts.EventType) : Bool := eventTypeCode t ∈ [25, 32]

/-! ## Common header and footer -/

/-- The 19-byte common header with the fields of `h`. -/
def evHeaderEnc (h : binlog.events.BinlogEventHeader) : List U8 :=
  leBytes 4 h.timestamp.1.val ++ [h.event_type.1] ++ leBytes 4 h.server_id.1.val ++
    leBytes 4 h.event_size.1.val ++ leBytes 4 h.log_pos.1.val ++ leBytes 2 h.flags.1.val

/-- The raw checksum algorithm code of a footer, if any. -/
def footerAlg (f : binlog.events.BinlogEventFooter) : Option Nat := f.checksum_alg.map (·.1.val)

/-- Whether an event of type code `ty` with footer `f` carries a checksum: the footer names an
    algorithm, and either it is not `OFF` or the event is a `FORMAT_DESCRIPTION_EVENT` (whose
    checksum is always present, WL#2540).  This is
    regardless of `checksum_enabled` (which `Event::read` honours when stripping the checksum). -/
def evHasChecksum (f : binlog.events.BinlogEventFooter) (ty : Nat) : Bool :=
  match footerAlg f with
  | some a => ty = 15 || a ≠ 0
  | none => false

/-- The serialized length of an event (`Event::len`): header, data, and with a known checksum
    algorithm the algorithm byte (FDE only) and the checksum (FDE, or algorithm not `OFF`); capped
    at `u32::MAX - 19` (the crate's cap). An unknown algorithm counts no footer.  Regardless of
    `checksum_enabled`. -/
def eventLen (e : binlog.events.Event) : Nat :=
  let isFde := e.header.event_type.1.val = 15
  let foot : Nat := match (footerAlg e.footer).bind checksumAlgOfCode with
    | some a => (if isFde then 1 else 0) + (if isFde ∨ checksumAlgCode a ≠ 0 then 4 else 0)
    | none => 0
  min (19 + e.data.length + foot) evLenCap

/-! ## `FORMAT_DESCRIPTION_EVENT` -/

open binlog.consts.EventType in
/-- The post-header length of each event type when the FDE's `post_header_len` array does not
    cover it (`get_event_type_header_length`'s defaults, the libbinlogevents constants:
    `QUERY_HEADER_LEN` 13, `ROTATE_HEADER_LEN` 8, `START_V3_HEADER_LEN` 56, the FDE's
    `56 + 43`, `ROWS_HEADER_LEN_V1` 8, `ROWS_HEADER_LEN_V2` 10, `GTID_HEADER_LEN` 42, …). The crate
    uses 0 for the pre-5.0 `LOAD`/`CREATE_FILE`/`EXEC_LOAD`/`NEW_LOAD` events and for
    `GTID_TAGGED_LOG_EVENT` (variable). -/
def defaultPostHeaderLen : binlog.consts.EventType → Nat
  | START_EVENT_V3 => 56 | QUERY_EVENT => 13 | ROTATE_EVENT => 8 | APPEND_BLOCK_EVENT => 4
  | DELETE_FILE_EVENT => 4 | FORMAT_DESCRIPTION_EVENT => 99 | BEGIN_LOAD_QUERY_EVENT => 4
  | EXECUTE_LOAD_QUERY_EVENT => 26 | TABLE_MAP_EVENT => 8 | WRITE_ROWS_EVENT_V1 => 8
  | UPDATE_ROWS_EVENT_V1 => 8 | DELETE_ROWS_EVENT_V1 => 8 | INCIDENT_EVENT => 2
  | WRITE_ROWS_EVENT => 10 | UPDATE_ROWS_EVENT => 10 | DELETE_ROWS_EVENT => 10
  | GTID_EVENT => 42 | ANONYMOUS_GTID_EVENT => 42 | TRANSACTION_CONTEXT_EVENT => 18
  | VIEW_CHANGE_EVENT => 52 | PARTIAL_UPDATE_ROWS_EVENT => 10
  | _ => 0

/-- The post-header length of event type `t` given the FDE's array `lens`: `lens[code - 1]`,
    or the default if the array is shorter; `0` for `UNKNOWN_EVENT`. -/
def postHeaderLen (lens : List U8) (t : binlog.consts.EventType) : Nat :=
  if eventTypeCode t = 0 then 0
  else match lens[eventTypeCode t - 1]? with
    | some b => b.val
    | none => defaultPostHeaderLen t

/-- The FDE's post-header lengths array. -/
def fdeLens (fde : binlog.events.format_description_event.FormatDescriptionEvent) : List U8 :=
  cowList fde.event_type_header_lengths.1

/-- The fields of a format description event: binlog version, server version (all 50 bytes,
    padding included, as stored), creation timestamp, post-header lengths. -/
structure FdeView where
  version : binlog.consts.BinlogVersion
  serverVersion : List U8
  createTimestamp : Nat
  lens : List U8

/-- The fields of `e`. -/
def fdeView (e : binlog.events.format_description_event.FormatDescriptionEvent) : FdeView :=
  { version := e.binlog_version.1, serverVersion := cowList e.server_version.1,
    createTimestamp := e.create_timestamp.1.val, lens := fdeLens e }

/-- A format description event's data as the crate writes it. -/
def fdeEnc (e : binlog.events.format_description_event.FormatDescriptionEvent) : List U8 :=
  leBytes 2 (binlogVersionCode e.binlog_version.1) ++ fixedText 50 (cowList e.server_version.1) ++
    leBytes 4 e.create_timestamp.1.val ++ [byte 19] ++ fdeLens e

/-- The crate's reader of a format description event: 57 bytes of fixed fields, a known binlog
    version (1–4), a header length of exactly 19, and the rest of the data as the post-header
    lengths. (The footer is not read here: `Event::read` strips it.) -/
def fdeRead (bs : List U8) : Option (FdeView × List U8) :=
  if bs.length < 57 then none else
  match binlogVersionOfCode (leNat (bs.take 2)) with
  | none => none
  | some v =>
    if (bs[56]?.map (·.val)) ≠ some 19 then none
    else some ({ version := v, serverVersion := (bs.drop 2).take 50,
                 createTimestamp := leNat ((bs.drop 52).take 4), lens := bs.drop 57 }, [])

/-! ## `QUERY_EVENT` and status variables -/

/-- The fields of a query event (`status_vars_len` and `db_len` as stored). -/
structure QueryView where
  threadId : Nat
  execTime : Nat
  schemaLen : Nat
  errorCode : Nat
  statusVarsLen : Nat
  statusVars : List U8
  schema : List U8
  query : List U8

/-- The fields of a query event. -/
def queryView (e : binlog.events.query_event.QueryEvent) : QueryView :=
  { threadId := e.thread_id.1.val, execTime := e.execution_time.1.val,
    schemaLen := e.schema_len.1.val, errorCode := e.error_code.1.val,
    statusVarsLen := e.status_vars_len.1.val, statusVars := cowList e.status_vars.1,
    schema := cowList e.schema.1, query := cowList e.query.1 }

/-- A query event's data as the crate writes it: the stored `db_len` and `status_vars_len`
    (not recomputed), the status variables truncated to 65535 bytes, the schema to 255, a `0`. -/
def queryEnc (e : binlog.events.query_event.QueryEvent) : List U8 :=
  leBytes 4 e.thread_id.1.val ++ leBytes 4 e.execution_time.1.val ++ [e.schema_len.1] ++
    leBytes 2 e.error_code.1.val ++ leBytes 2 e.status_vars_len.1.val ++
    (cowList e.status_vars.1).take 65535 ++ (cowList e.schema.1).take 255 ++ [byte 0] ++
    cowList e.query.1

/-- The crate's reader of a query event whose post-header is `p` bytes long (from the FDE): the
    13 known post-header bytes, the rest of the post-header skipped, `status_vars_len` bytes of
    status variables, `db_len` bytes of schema, one byte skipped (**not checked to be `0`**), the
    query as the rest. **Crate deviation:** with a post-header shorter than 13 bytes (pre-5.0
    servers: 11) the crate still reads 13, so such events are misread. -/
def queryRead (p : Nat) (bs : List U8) : Option (QueryView × List U8) := do
  let (hd, r1) ← takeExact 13 bs
  let (_, r2) ← takeExact (p - 13) r1
  let svl := leNat ((hd.drop 11).take 2)
  let sl := (hd.drop 8).headD (byte 0)
  let (sv, r3) ← takeExact svl r2
  let (sc, r4) ← takeExact sl.val r3
  let (_, r5) ← takeExact 1 r4
  some ({ threadId := leNat (hd.take 4), execTime := leNat ((hd.drop 4).take 4),
          schemaLen := sl.val, errorCode := leNat ((hd.drop 9).take 2), statusVarsLen := svl,
          statusVars := sv, schema := sc, query := r5 }, [])

/-- The length of `count` `0`-terminated names at the front of `bs`, if they are all there. -/
def dbNamesLen : Nat → List U8 → Option Nat
  | 0, _ => some 0
  | c + 1, bs =>
    if hasNul bs then
      let k := (beforeZero bs).length + 1
      (dbNamesLen c (bs.drop k)).map (k + ·)
    else none

/-- The length of the value of status variable `k` at the front of `v` (the bytes after the key),
    if determined. **Crate deviation:** `Q_UPDATED_DB_NAMES` with the count 254
    (`OVER_MAX_DBS_IN_EVENT_MTS`, no names follow) is read as 254 names, which normally do not
    exist, so the walk stops there and every later status variable is lost. -/
def svValueLen (k : Nat) (v : List U8) : Option Nat :=
  if k = 0 then some 4 else if k = 1 then some 8
  else if k = 2 then v.head?.map (fun b => 1 + b.val + 1)
  else if k = 3 then some 4 else if k = 4 then some 6
  else if k = 5 ∨ k = 6 then v.head?.map (fun b => 1 + b.val)
  else if k = 7 ∨ k = 8 then some 2 else if k = 9 then some 8 else if k = 10 then some 4
  else if k = 11 then
    match v.head? with
    | none => none
    | some u => ((v.drop (1 + u.val)).head?).map (fun h => 1 + u.val + 1 + h.val)
  else if k = 12 then
    match v with
    | [] => none
    | c :: rest => (dbNamesLen c.val rest).map (1 + ·)
  else if k = 13 then some 3 else if k = 14 ∨ k = 15 then some 0
  else if k = 16 then some 1 else if k = 17 then some 8 else if k = 18 then some 2
  else some 1

/-- The status variables at the front of `bs` (with fuel): each key and its value, stopping
    (without error) at the first unknown key or truncated value. -/
def svWalk : Nat → List U8 → List (Nat × List U8)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, k :: rest =>
    if statusVarKeyOfCode k.val = none then [] else
    match svValueLen k.val rest with
    | none => []
    | some n => if n ≤ rest.length then (k.val, rest.take n) :: svWalk fuel (rest.drop n) else []

/-- The status variables of the block `bs`, as `StatusVarsIterator` yields them. -/
def statusVarsOf (bs : List U8) : List (Nat × List U8) := svWalk (bs.length + 1) bs

/-- One step of `StatusVarsIterator` at position `pos` in `bs`: the variable and the next
    position, or `none` at the end. -/
def svStep (bs : List U8) (pos : Nat) : Option ((Nat × List U8) × Nat) :=
  match (statusVarsOf (bs.drop pos)).head? with
  | some (k, v) => some ((k, v), pos + 1 + v.length)
  | none => none

/-- A decoded status variable: its key code, numbers and byte strings (`StatusVarVal` flattened). -/
abbrev SvView := Nat × List Nat × List (List U8)

/-- The flattened contents of a `StatusVarVal`. -/
def svValView : binlog.events.query_event.StatusVarVal → SvView
  | .Flags2 f => (0, [f.1.val], [])
  | .SqlMode f => (1, [f.1.val], [])
  | .Catalog s => (2, [], [s.val])
  | .AutoIncrement i o => (3, [i.val, o.val], [])
  | .Charset a b c => (4, [a.val, b.val, c.val], [])
  | .TimeZone s => (5, [], [cowList s.1])
  | .CatalogNz s => (6, [], [cowList s.1])
  | .LcTimeNames x => (7, [x.val], [])
  | .CharsetDatabase x => (8, [x.val], [])
  | .TableMapForUpdate x => (9, [x.val], [])
  | .MasterDataWritten a => (10, [], [a.val])
  | .Invoker u h => (11, [], [cowList u.1, cowList h.1])
  | .UpdatedDbNames ns => (12, [], ns.val.map (fun n => cowList n.1))
  | .Microseconds x => (13, [x.val], [])
  | .CommitTs s => (14, [], [s.val])
  | .CommitTs2 s => (15, [], [s.val])
  | .ExplicitDefaultsForTimestamp b => (16, [if b then 1 else 0], [])
  | .DdlLoggedWithXid x => (17, [x.val], [])
  | .DefaultCollationForUtf8mb4 x => (18, [x.val], [])
  | .SqlRequirePrimaryKey x => (19, [x.val], [])
  | .DefaultTableEncryption x => (20, [x.val], [])

/-- A 1-byte-length-prefixed string at the front of `v` (extra bytes after it ignored). -/
def lp1 (v : List U8) : Option (List U8 × List U8) :=
  match v with
  | [] => none
  | n :: r => takeExact n.val r

/-- `count` `0`-terminated names at the front of `bs` (the format of `Q_UPDATED_DB_NAMES`). -/
def dbNames : Nat → List U8 → Option (List (List U8))
  | 0, _ => some []
  | c + 1, bs => if hasNul bs then (dbNames c (bs.drop ((beforeZero bs).length + 1))).map
      (beforeZero bs :: ·) else none

/-- `Q_UPDATED_DB_NAMES` as the crate reads it (`updated_db_names`, **upstream bug**: after a
    name it does not skip the `0` terminator, so every later name is read as empty): for a count
    `c ≥ 1`, the bytes before the first `0` and then `c - 1` empty names; `none` without a `0`. -/
def dbNamesCrate (c : Nat) (bs : List U8) : Option (List (List U8)) :=
  if c = 0 then some [] else if hasNul bs then some (beforeZero bs :: List.replicate (c - 1) [])
  else none

/-- The value of status variable `k` decoded from `v` per the format (extra bytes ignored):
    integers little-endian, strings with their 1-byte length; `Catalog`, `CommitTs`,
    `CommitTs2` keep the raw value; `Q_MICROSECONDS` is a 3-byte integer;
    `Q_UPDATED_DB_NAMES` is a count and that many `0`-terminated names, where the count 254
    (`OVER_MAX_DBS_IN_EVENT_MTS`) means that no names follow (no names). The statements use it
    only for keys other than 12 and 13 (the crate's decoding of those two is stated separately). -/
def svValRead (k : Nat) (v : List U8) : Option SvView :=
  let int (w : Nat) : Option Nat := if w ≤ v.length then some (leNat (v.take w)) else none
  if k = 0 then (int 4).map (fun x => (0, [x], []))
  else if k = 1 then (int 8).map (fun x => (1, [x], []))
  else if k = 2 then some (2, [], [v])
  else if k = 3 then if 4 ≤ v.length then some (3, [leNat (v.take 2), leNat ((v.drop 2).take 2)], []) else none
  else if k = 4 then if 6 ≤ v.length then
      some (4, [leNat (v.take 2), leNat ((v.drop 2).take 2), leNat ((v.drop 4).take 2)], []) else none
  else if k = 5 ∨ k = 6 then (lp1 v).map (fun (s, _) => (k, [], [s]))
  else if k = 7 ∨ k = 8 then (int 2).map (fun x => (k, [x], []))
  else if k = 9 then (int 8).map (fun x => (9, [x], []))
  else if k = 10 then if 4 ≤ v.length then some (10, [], [v.take 4]) else none
  else if k = 11 then
    match lp1 v with
    | none => none
    | some (u, r) => (lp1 r).map (fun (h, _) => (11, [], [u, h]))
  else if k = 12 then
    match v with
    | [] => none
    | c :: r => if c.val = 254 then some (12, [], []) else (dbNames c.val r).map (fun ns => (12, [], ns))
  else if k = 13 then (int 3).map (fun x => (13, [x], []))
  else if k = 14 ∨ k = 15 then some (k, [], [v])
  else if k = 16 then (int 1).map (fun x => (16, [if x = 0 then 0 else 1], []))
  else if k = 17 then (int 8).map (fun x => (17, [x], []))
  else if k = 18 then (int 2).map (fun x => (18, [x], []))
  else if k = 19 then (int 1).map (fun x => (19, [x], []))
  else (int 1).map (fun x => (20, [x], []))

/-! ## Small events -/

/-- A rotate event's data: `position` (8), the next log's name (rest). -/
def rotateEnc (e : binlog.events.rotate_event.RotateEvent) : List U8 :=
  leBytes 8 e.position.1.val ++ cowList e.name.1

/-- The crate's rotate reader: 8 bytes of position, the name as the rest. -/
def rotateRead (bs : List U8) : Option ((Nat × List U8) × List U8) :=
  if 8 ≤ bs.length then some ((leNat (bs.take 8), bs.drop 8), []) else none

/-- The fields of a rotate event. -/
def rotateView (e : binlog.events.rotate_event.RotateEvent) : Nat × List U8 :=
  (e.position.1.val, cowList e.name.1)

/-- An intvar event's data: the subtype (1) and the value (8). -/
def intvarEnc (e : binlog.events.intvar_event.IntvarEvent) : List U8 :=
  byte (intvarTypeCode e.subtype.1) :: leBytes 8 e.value.1.val

/-- The crate's intvar reader (9 bytes): a known subtype and the value. -/
def intvarRead (bs : List U8) : Option ((binlog.consts.IntvarEventType × Nat) × List U8) :=
  if bs.length < 9 then none else
  match bs.head?.bind (fun b => intvarTypeOfCode b.val) with
  | some t => some ((t, leNat ((bs.drop 1).take 8)), bs.drop 9)
  | none => none

/-- A rand event's data: the two seeds. -/
def randEnc (e : binlog.events.rand_event.RandEvent) : List U8 :=
  leBytes 8 e.seed1.1.val ++ leBytes 8 e.seed2.1.val

/-- The crate's XID reader, after a post-header of `p` bytes: the 8-byte XID. -/
def xidRead (p : Nat) (bs : List U8) : Option (Nat × List U8) :=
  if p + 8 ≤ bs.length then some (leNat ((bs.drop p).take 8), bs.drop (p + 8)) else none

/-- An incident event's data: the type (2) and the message with a 1-byte length (truncated to
    255 bytes). -/
def incidentEnc (e : binlog.events.incident_event.IncidentEvent) : List U8 :=
  leBytes 2 e.incident_type.1.val ++ u8Str (cowList e.message.1)

/-- The crate's incident reader: the raw type (2) and the length-prefixed message; bytes after
    it are left. -/
def incidentRead (bs : List U8) : Option ((Nat × List U8) × List U8) := do
  let (t, r) ← takeExact 2 bs
  let (m, r') ← optFst (checkedLenPrefixed 1 r)
  some ((leNat t, m), r')

/-- A rows-query event's data: a `0` length byte and the query. -/
def rowsQueryEnc (e : binlog.events.rows_query_event.RowsQueryEvent) : List U8 :=
  byte 0 :: cowList e.query.1

/-- A begin-load-query event's data: `file_id` (4) and the block. -/
def beginLoadQueryEnc (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) : List U8 :=
  leBytes 4 e.file_id.1.val ++ cowList e.block_data.1

/-- The fields of an execute-load-query event: the query fields and `file_id`, `start_pos`,
    `end_pos`, `dup_handling`. -/
structure ElqView where
  q : QueryView
  fileId : Nat
  startPos : Nat
  endPos : Nat
  dup : Nat

/-- The fields of an execute-load-query event. -/
def elqView (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) : ElqView :=
  { q := { threadId := e.thread_id.1.val, execTime := e.execution_time.1.val,
           schemaLen := e.schema_len.1.val, errorCode := e.error_code.1.val,
           statusVarsLen := e.status_vars_len.1.val, statusVars := cowList e.status_vars.1,
           schema := cowList e.schema.1, query := cowList e.query.1 },
    fileId := e.file_id.1.val, startPos := e.start_pos.1.val, endPos := e.end_pos.1.val,
    dup := loadDupCode e.dup_handling.1 }

/-- An execute-load-query event's data as the crate writes it. -/
def elqEnc (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) : List U8 :=
  leBytes 4 e.thread_id.1.val ++ leBytes 4 e.execution_time.1.val ++ [e.schema_len.1] ++
    leBytes 2 e.error_code.1.val ++ leBytes 2 e.status_vars_len.1.val ++
    leBytes 4 e.file_id.1.val ++ leBytes 4 e.start_pos.1.val ++ leBytes 4 e.end_pos.1.val ++
    [byte (loadDupCode e.dup_handling.1)] ++
    (cowList e.status_vars.1).take 65535 ++ (cowList e.schema.1).take 255 ++ [byte 0] ++
    cowList e.query.1

/-- The crate's execute-load-query reader: the 26-byte post-header (a known `dup_handling`,
    0–2; **the FDE's post-header length is ignored**), then as `queryRead`. -/
def elqRead (bs : List U8) : Option (ElqView × List U8) := do
  let (hd, r1) ← takeExact 26 bs
  let d := ((hd.drop 25).headD (byte 0)).val
  if 2 < d then none else
  let svl := leNat ((hd.drop 11).take 2)
  let sl := (hd.drop 8).headD (byte 0)
  let (sv, r2) ← takeExact svl r1
  let (sc, r3) ← takeExact sl.val r2
  let (_, r4) ← takeExact 1 r3
  some ({ q := { threadId := leNat (hd.take 4), execTime := leNat ((hd.drop 4).take 4),
                 schemaLen := sl.val, errorCode := leNat ((hd.drop 9).take 2),
                 statusVarsLen := svl, statusVars := sv, schema := sc, query := r4 },
          fileId := leNat ((hd.drop 13).take 4), startPos := leNat ((hd.drop 17).take 4),
          endPos := leNat ((hd.drop 21).take 4), dup := d }, [])

/-! ## GTID events (untagged format) -/

/-- `UNDEFINED_SERVER_VERSION`. -/
def undefinedServerVersion : Nat := 999999

/-- The fields of a GTID event (untagged format). `lc` says whether the logical-clock part
    (`lt_type` and what follows) is present. -/
structure GtidView where
  flags : Nat
  sid : List U8
  gno : Nat
  lc : Bool
  lastCommitted : Nat
  sequenceNumber : Nat
  immediateCommitTs : Nat
  originalCommitTs : Nat
  txLength : Nat
  immediateServerVersion : Nat
  originalServerVersion : Nat

/-- The fields of a GTID event. -/
def gtidView (e : binlog.events.gtid_event.GtidEvent) : GtidView :=
  { flags := e.flags.1.val, sid := e.sid.val, gno := e.gno.1.val, lc := e.lc_typecode.isSome,
    lastCommitted := e.last_committed.1.val, sequenceNumber := e.sequence_number.1.val,
    immediateCommitTs := e.immediate_commit_timestamp.1.val,
    originalCommitTs := e.original_commit_timestamp.1.val, txLength := e.tx_length.1.val,
    immediateServerVersion := e.immediate_server_version.1.val,
    originalServerVersion := e.original_server_version.1.val }

/-- An untagged GTID event's data as the crate writes it: without a logical-clock part only the
    25-byte post-header prefix; otherwise the format above, with bit 55 (31) of the immediate
    timestamp (server version) set iff it differs from the original, which then follows. -/
def gtidEnc (e : binlog.events.gtid_event.GtidEvent) : List U8 :=
  let ict := e.immediate_commit_timestamp.1.val
  let oct := e.original_commit_timestamp.1.val
  let isv := e.immediate_server_version.1.val
  let osv := e.original_server_version.1.val
  [e.flags.1] ++ e.sid.val ++ leBytes 8 e.gno.1.val ++
  match e.lc_typecode with
  | none => []
  | some _ =>
    [byte 2] ++ leBytes 8 e.last_committed.1.val ++ leBytes 8 e.sequence_number.1.val ++
      leBytes 7 (ict % 2 ^ 55 + if ict ≠ oct then 2 ^ 55 else 0) ++
      (if ict ≠ oct then leBytes 7 oct else []) ++ lenencInt e.tx_length.1.val ++
      leBytes 4 (isv % 2 ^ 31 + if isv ≠ osv then 2 ^ 31 else 0) ++
      (if isv ≠ osv then leBytes 4 osv else [])

/-- The crate's untagged GTID reader. 25 bytes are required. The logical-clock part is read iff
    the next byte is `2`; then 16 bytes are required, and each later field is read only if enough
    bytes remain (7 for the timestamp, 1 for the transaction length, 4 for the server version);
    an announced original timestamp (server version) must be there. Absent fields are 0, absent
    server versions `UNDEFINED_SERVER_VERSION`. Bytes after the last field read are left (MySQL
    8.0.33+ may follow with `commit_group_ticket`, which is not read). -/
def gtidRead (bs : List U8) : Option (GtidView × List U8) :=
  if bs.length < 25 then none else
  let flags := (bs.headD (byte 0)).val
  let sid := (bs.drop 1).take 16
  let gno := leNat ((bs.drop 17).take 8)
  let r := bs.drop 25
  let noLc : GtidView :=
    { flags := flags, sid := sid, gno := gno, lc := false, lastCommitted := 0,
      sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
      immediateServerVersion := undefinedServerVersion,
      originalServerVersion := undefinedServerVersion }
  match r with
  | b :: r1 =>
    if b.val ≠ 2 then some (noLc, r) else
    if r1.length < 16 then none else
    let r2 := r1.drop 16
    let ts : Option (Nat × Nat × List U8) :=
      if 7 ≤ r2.length then
        let raw := leNat (r2.take 7)
        if raw.testBit 55 then
          (if 7 ≤ (r2.drop 7).length then some (raw - 2 ^ 55, leNat ((r2.drop 7).take 7), r2.drop 14)
           else none)
        else some (raw, raw, r2.drop 7)
      else some (0, 0, r2)
    match ts with
    | none => none
    | some (ict, oct, r3) =>
      let tx : Option (Nat × List U8) := match r3 with
        | [] => some (0, [])
        | _ => optFst (checkedLenencInt r3)
      match tx with
      | none => none
      | some (txl, r4) =>
        let sv : Option (Nat × Nat × List U8) :=
          if 4 ≤ r4.length then
            let raw := leNat (r4.take 4)
            if raw.testBit 31 then
              (if 4 ≤ (r4.drop 4).length then some (raw - 2 ^ 31, leNat ((r4.drop 4).take 4), r4.drop 8)
               else none)
            else some (raw, raw, r4.drop 4)
          else some (undefinedServerVersion, undefinedServerVersion, r4)
        sv.map (fun (isv, osv, r5) =>
          ({ flags := flags, sid := sid, gno := gno, lc := true, lastCommitted := leNat (r1.take 8),
             sequenceNumber := leNat ((r1.drop 8).take 8), immediateCommitTs := ict,
             originalCommitTs := oct, txLength := txl, immediateServerVersion := isv,
             originalServerVersion := osv }, r5))
  | [] => some (noLc, [])

/-- The length `GtidEvent::len` counts for an untagged event: always the logical-clock part
    (even when it is absent), capped. -/
def gtidLenCrate (e : binlog.events.gtid_event.GtidEvent) : Nat :=
  let ict := e.immediate_commit_timestamp.1.val
  let oct := e.original_commit_timestamp.1.val
  let isv := e.immediate_server_version.1.val
  let osv := e.original_server_version.1.val
  min (1 + 16 + 8 + 1 + 8 + 8 + 7 + (if ict ≠ oct then 7 else 0) +
    (lenencInt e.tx_length.1.val).length + 4 + (if isv ≠ osv then 4 else 0)) evLenCap

/-! ## `PREVIOUS_GTIDS_LOG_EVENT` (untagged format) -/

/-- A GNO interval: `start` (8), `end` (8). -/
def gnoIntervalEnc (i : packets.GnoInterval) : List U8 :=
  leBytes 8 i.start.1.val ++ leBytes 8 i.«end».1.val

/-- A SID entry in the untagged format. -/
def pgSidEnc (s : binlog.events.previous_gtids_event.PreviousGtidsSid) : List U8 :=
  s.uuid.val ++ leBytes 8 s.intervals.length ++ (s.intervals.val.map gnoIntervalEnc).flatten

/-- An untagged previous-GTIDs event: the count (8) and the SIDs. -/
def pgEnc (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) : List U8 :=
  leBytes 8 e.sids.length ++ (e.sids.val.map pgSidEnc).flatten

/-- A SID entry as plain data: the UUID and the `(start, end)` of each interval. -/
abbrev PgSidView := List U8 × List (Nat × Nat)

/-- The data of a SID entry (its tag aside). -/
def pgSidView (s : binlog.events.previous_gtids_event.PreviousGtidsSid) : PgSidView :=
  (s.uuid.val, s.intervals.val.map (fun i => (i.start.1.val, i.«end».1.val)))

/-- `n` intervals of 16 bytes. -/
def pgIntervalsRead : Nat → List U8 → Option (List (Nat × Nat) × List U8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    if 16 ≤ bs.length then
      (pgIntervalsRead n (bs.drop 16)).map
        (fun (is, r) => ((leNat (bs.take 8), leNat ((bs.drop 8).take 8)) :: is, r))
    else none

/-- `n` untagged SID entries. -/
def pgSidsRead : Nat → List U8 → Option (List PgSidView × List U8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    if bs.length < 24 then none else
    match pgIntervalsRead (leNat ((bs.drop 16).take 8)) (bs.drop 24) with
    | none => none
    | some (is, r) => (pgSidsRead n r).map (fun (ss, r') => ((bs.take 16, is) :: ss, r'))

/-- The crate's reader of an untagged previous-GTIDs event (byte 7 of the count is `0`): 8 bytes
    of count (its low 56 bits), then that many SID entries; bytes after them are left. -/
def pgRead (bs : List U8) : Option (List PgSidView × List U8) :=
  if bs.length < 8 then none else pgSidsRead (leNat (bs.take 8) % 2 ^ 56) (bs.drop 8)

/-! ## `TABLE_MAP_EVENT` -/

/-- The fields of a table map event (counts as stored, byte strings in full). -/
structure TmView where
  tableId : Nat
  flags : Nat
  db : List U8
  table : List U8
  columnCount : Nat
  types : List U8
  mdata : List U8
  nullBitmap : List U8
  optMeta : List U8

/-- The fields of a table map event. -/
def tmView (e : binlog.events.table_map_event.TableMapEvent) : TmView :=
  { tableId := e.table_id.1.val, flags := e.flags.1.val, db := cowList e.database_name.1,
    table := cowList e.table_name.1, columnCount := e.columns_count.1.val,
    types := cowList e.columns_type.1, mdata := cowList e.columns_metadata.1,
    nullBitmap := cowList e.null_bitmask.1, optMeta := cowList e.optional_metadata.1 }

/-- A table map event's data as the crate writes it (names truncated to 255 bytes, each followed
    by `0`). -/
def tmEnc (e : binlog.events.table_map_event.TableMapEvent) : List U8 :=
  leBytes 6 e.table_id.1.val ++ leBytes 2 e.flags.1.val ++ u8Str (cowList e.database_name.1) ++
    [byte 0] ++ u8Str (cowList e.table_name.1) ++ [byte 0] ++ lenencInt e.columns_count.1.val ++
    cowList e.columns_type.1 ++ lenencStr (cowList e.columns_metadata.1) ++
    (cowList e.null_bitmask.1).take (2 ^ 61) ++ cowList e.optional_metadata.1

/-- The crate's table map reader, post-header `p` bytes long (from the FDE): `table_id` of 4
    bytes if `p = 6`, else 6; the names' terminators are skipped **unchecked**; the counts read
    with the crate's lenenc readers (`checkedLenencInt`, `checkedLenencStr`); `(n + 7) / 8`
    bitmap bytes; the optional metadata as the rest. -/
def tmRead (p : Nat) (bs : List U8) : Option (TmView × List U8) := do
  let (tid, r1) ← if p = 6 then readLE 4 bs else readLE 6 bs
  let (fl, r2) ← readLE 2 r1
  let (db, r3) ← optFst (checkedLenPrefixed 1 r2)
  let (_, r4) ← takeExact 1 r3
  let (tb, r5) ← optFst (checkedLenPrefixed 1 r4)
  let (_, r6) ← takeExact 1 r5
  let (n, r7) ← optFst (checkedLenencInt r6)
  let (ty, r8) ← takeExact n r7
  let (me, r9) ← optFst (checkedLenencStr r8)
  let (nb, r10) ← takeExact ((n + 7) / 8) r9
  some ({ tableId := tid, flags := fl, db := db, table := tb, columnCount := n, types := ty,
          mdata := me, nullBitmap := nb, optMeta := r10 }, [])

/-- A table map event as read from the wire is consistent: names of at most 255 bytes, one type
    byte per column and a `(n + 7) / 8`-byte NULL bitmap. -/
def TmConsistent (e : binlog.events.table_map_event.TableMapEvent) : Prop :=
  (cowList e.database_name.1).length ≤ 255 ∧ (cowList e.table_name.1).length ≤ 255 ∧
  (cowList e.columns_type.1).length = e.columns_count.1.val ∧
  (cowList e.null_bitmask.1).length = (e.columns_count.1.val + 7) / 8

/-- The length `TableMapEvent::len` returns: the encoded length, except that the NULL bitmap is
    counted as `(n + 8) / 7` bytes instead of `(n + 7) / 8` (**upstream bug**), capped. -/
def tmLenCrate (e : binlog.events.table_map_event.TableMapEvent) : Nat :=
  let n := e.columns_count.1.val
  min (6 + 2 + 1 + min (cowList e.database_name.1).length 255 + 1 + 1 +
    min (cowList e.table_name.1).length 255 + 1 + (lenencInt n).length + n +
    (lenencStr (cowList e.columns_metadata.1)).length + (n + 8) / 7 +
    (cowList e.optional_metadata.1).length) evLenCap

open constants.ColumnType in
/-- The number of metadata bytes of a column of type `t` in a table map's metadata block
    (`is_array`: inside a `TYPED_ARRAY`). This **transcribes the crate's
    `ColumnType::get_metadata`** (`binlog/mod.rs`), which `TableMapEvent::get_column_metadata`
    uses to walk the block: 1 for the BLOB types, `FLOAT`, `DOUBLE`, `GEOMETRY`, `JSON`, `VECTOR`
    and the fractional temporal types; 2 for `VARCHAR` (3 inside an array), `NEWDECIMAL`, `SET`,
    `ENUM`, `STRING`, `BIT`; 0 otherwise (`TYPED_ARRAY` is handled by `tmColumnMeta`). It agrees
    with MySQL's `Field::save_field_metadata`, except that the 3 bytes of an array `VARCHAR` are
    unverified. It is not E1's `binlogMetaLen` (`Defs/BinlogValue.lean`: how many metadata bytes
    the *value decoder* reads), which differs on `FLOAT`, `DOUBLE`, `JSON`, `VAR_STRING` and array
    `VARCHAR`. -/
def getMetadataLen (t : constants.ColumnType) (isArray : Bool) : Nat :=
  match t with
  | MYSQL_TYPE_TINY_BLOB | MYSQL_TYPE_BLOB | MYSQL_TYPE_MEDIUM_BLOB | MYSQL_TYPE_LONG_BLOB
  | MYSQL_TYPE_DOUBLE | MYSQL_TYPE_FLOAT | MYSQL_TYPE_GEOMETRY | MYSQL_TYPE_TIME2
  | MYSQL_TYPE_DATETIME2 | MYSQL_TYPE_TIMESTAMP2 | MYSQL_TYPE_JSON | MYSQL_TYPE_VECTOR => 1
  | MYSQL_TYPE_VARCHAR => if isArray then 3 else 2
  | MYSQL_TYPE_NEWDECIMAL | MYSQL_TYPE_SET | MYSQL_TYPE_ENUM | MYSQL_TYPE_STRING
  | MYSQL_TYPE_BIT => 2
  | _ => 0

/-- The metadata of a column of type code `ty` at the front of `ptr` (`isArray`: inside a
    `TYPED_ARRAY`), with the number of bytes it occupies: `getMetadataLen` bytes; for
    `TYPED_ARRAY` (20) the element type byte, then the element type's metadata (array form),
    which is what is returned. `none` if `ptr` is too short or a type is unknown.
    **Upstream inconsistency:** the element metadata is returned *without* the element type byte,
    but the value decoder (`binlog/value.rs:59`, `binlogEffType` in `Defs/BinlogValue.lean`) reads
    `col_meta[0]` of a `TYPED_ARRAY` column as the element type. -/
def tmColumnMeta (isArray : Bool) (ty : Nat) (ptr : List U8) : Option (List U8 × Nat) :=
  match columnTypeOfCode ty with
  | none => none
  | some t =>
    if ty = 20 then
      match ptr with
      | [] => none
      | e :: rest => (tmColumnMeta true e.val rest).map (fun p => (p.1, p.2 + 1))
    else (takeExact (getMetadataLen t isArray) ptr).map (fun p => (p.1, getMetadataLen t isArray))
termination_by ptr.length

/-- The metadata of column `i` given the column type codes `types` and the metadata block `mdata`
    (`TableMapEvent::get_column_metadata`): the columns' metadata are consecutive; `none` past the
    last column, at an unknown type, or if the block is too short. -/
def tmMetaAt : List U8 → List U8 → Nat → Option (List U8)
  | [], _, _ => none
  | ty :: tys, mdata, i =>
    match tmColumnMeta false ty.val mdata with
    | none => none
    | some (m, k) => if i = 0 then some m else tmMetaAt tys (mdata.drop k) (i - 1)

/-- The type of a `STRING` column as the table map's metadata reveals it (MySQL's `real_type`):
    the first metadata byte, if non-zero, with bits `0x30` set (long `CHAR` columns store length
    bits there), must be `ENUM` (247), `SET` (248) or `STRING` (254); a zero byte means `STRING`.
    `none`: any other value (`BadColumnType::Unexpected`). -/
def tmStringRealType (f1 : Nat) : Option constants.ColumnType :=
  let r := if f1 ≠ 0 then f1 ||| 0x30 else 254
  if r = 247 then some .MYSQL_TYPE_ENUM else if r = 248 then some .MYSQL_TYPE_SET
  else if r = 254 then some .MYSQL_TYPE_STRING else none

/-! ## Rows events -/

/-- The fields of a rows event: its type, `table_id`, `flags`, extra data, column count, the
    column bitmaps present, the rows (raw). -/
structure RowsView where
  typeCode : Nat
  tableId : Nat
  flags : Nat
  extra : List U8
  numColumns : Nat
  before : Option (List U8)
  after : Option (List U8)
  rows : List U8

/-- The fields of a rows event. -/
def rowsView (e : binlog.events.rows_event.RowsEvent) : RowsView :=
  { typeCode := eventTypeCode e.event_type, tableId := e.table_id.1.val, flags := e.flags.1.val,
    extra := cowList e.extra_data.1, numColumns := e.num_columns.1.val,
    before := e.columns_before_image.map (fun b => cowList b.1),
    after := e.columns_after_image.map (fun b => cowList b.1), rows := cowList e.rows_data.1 }

/-- A rows event's data as the crate writes it: `table_id` (6), `flags` (2), for v2 types the
    extra-data length (counting its 2 bytes) and the extra data (at most 65533 bytes), the column
    count, the bitmaps present (at most `2^61` bytes each), the rows. -/
def rowsEnc (e : binlog.events.rows_event.RowsEvent) : List U8 :=
  let ex := cowList e.extra_data.1
  leBytes 6 e.table_id.1.val ++ leBytes 2 e.flags.1.val ++
    (if rowsIsV2 e.event_type then leBytes 2 (min ex.length 65533 + 2) ++ ex.take 65533 else []) ++
    lenencInt e.num_columns.1.val ++
    (e.columns_before_image.map (fun b => (cowList b.1).take (2 ^ 61))).getD [] ++
    (e.columns_after_image.map (fun b => (cowList b.1).take (2 ^ 61))).getD [] ++
    cowList e.rows_data.1

/-- The crate's reader of a rows event of type `t` whose post-header is `p` bytes and the
    `WRITE_ROWS_EVENT` (v2) post-header `pw` bytes (both from the FDE): `table_id` of 4 bytes if
    `p = 6`, else 6; `flags`; extra data iff `p = pw` (its length counts its own 2 bytes; a length
    below 2 means none); the column count; `(n + 7) / 8` bytes per bitmap (two for update events,
    the before-image for delete events, the after-image otherwise); the rows as the rest. -/
def rowsRead (t : binlog.consts.EventType) (p pw : Nat) (bs : List U8) :
    Option (RowsView × List U8) := do
  let (tid, r1) ← if p = 6 then readLE 4 bs else readLE 6 bs
  let (fl, r2) ← readLE 2 r1
  let (ex, r3) ← if p = pw then (do
      let (l, r) ← readLE 2 r2
      takeExact (l - 2) r) else some ([], r2)
  let (n, r4) ← optFst (checkedLenencInt r3)
  let bl := (n + 7) / 8
  let (bf, r5) ← if rowsIsUpdate t || rowsIsDelete t then
      (takeExact bl r4).map (fun p => (some p.1, p.2)) else some (none, r4)
  let (af, r6) ← if rowsIsDelete t then some (none, r5) else
      (takeExact bl r5).map (fun p => (some p.1, p.2))
  some ({ typeCode := eventTypeCode t, tableId := tid, flags := fl, extra := ex, numColumns := n,
          before := bf, after := af, rows := r6 }, [])

/-- A rows event as read from the wire is consistent: extra data of at most 65533 bytes (none for
    v1 types), bitmaps of `(n + 7) / 8` bytes, before-image iff update or delete, after-image iff
    not delete. -/
def RowsConsistent (e : binlog.events.rows_event.RowsEvent) : Prop :=
  let bl := (e.num_columns.1.val + 7) / 8
  (cowList e.extra_data.1).length ≤ 65533 ∧
  (rowsIsV2 e.event_type = false → cowList e.extra_data.1 = []) ∧
  (e.columns_before_image.map (fun b => (cowList b.1).length) =
    if rowsIsUpdate e.event_type || rowsIsDelete e.event_type then some bl else none) ∧
  (e.columns_after_image.map (fun b => (cowList b.1).length) =
    if rowsIsDelete e.event_type then none else some bl)

/-- The length `RowsEvent::len` returns: 2 bytes of extra-data length and the extra data are
    counted **for every type, v1 included** (where nothing is written), and each bitmap present
    as `(n + 7) / 8` bytes; capped. -/
def rowsLenCrate (e : binlog.events.rows_event.RowsEvent) : Nat :=
  let n := e.num_columns.1.val
  let bl := (n + 7) / 8
  min (6 + 2 + 2 + min (cowList e.extra_data.1).length 65533 + (lenencInt n).length +
    (if e.columns_before_image.isSome then bl else 0) +
    (if e.columns_after_image.isSome then bl else 0) + (cowList e.rows_data.1).length) evLenCap

/-- The rows event inside a `RowsEventData` (every variant wraps a `RowsEvent`). -/
def rowsInner : binlog.events.RowsEventData → binlog.events.rows_event.RowsEvent
  | .WriteRowsEventV1 e | .UpdateRowsEventV1 e | .DeleteRowsEventV1 e | .WriteRowsEvent e
  | .UpdateRowsEvent e | .DeleteRowsEvent e | .PartialUpdateRowsEvent e => e

/-- The event type code of each `RowsEventData` variant (by constructor). -/
def rowsVariantCode : binlog.events.RowsEventData → Nat
  | .WriteRowsEventV1 _ => 23 | .UpdateRowsEventV1 _ => 24 | .DeleteRowsEventV1 _ => 25
  | .WriteRowsEvent _ => 30 | .UpdateRowsEvent _ => 31 | .DeleteRowsEvent _ => 32
  | .PartialUpdateRowsEvent _ => 39

/-! ## `TRANSACTION_PAYLOAD_EVENT` -/

/-- A header field: its type, the length of its value and the value, each length-encoded. -/
def tpField (ty v : Nat) : List U8 := lenencInt ty ++ lenencInt (lenencInt v).length ++ lenencInt v

/-- A transaction payload event's data as the crate writes it: the compression type, the
    uncompressed size (only when compressed), the payload size (as stored, not recomputed), the
    end mark, the payload. -/
def tpEnc (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) : List U8 :=
  tpField 2 (txCompressionCode e.algorithm) ++
    (if txCompressionCode e.algorithm = 255 then [] else tpField 3 e.uncompressed_size.1.val) ++
    tpField 1 e.payload_size.1.val ++ lenencInt 0 ++ cowList e.payload.1

/-! ## `EventData` -/

/-- The raw data of the `EventData` variants that keep it uninterpreted. -/
def edRaw : binlog.events.EventData → Option (List U8)
  | .StartEventV3 c | .LoadEvent c | .CreateFileEvent c | .AppendBlockEvent c | .ExecLoadEvent c
  | .DeleteFileEvent c | .NewLoadEvent c | .PreGaWriteRowsEvent c | .PreGaUpdateRowsEvent c
  | .PreGaDeleteRowsEvent c | .IgnorableEvent c | .TransactionContextEvent c
  | .ViewChangeEvent c | .XaPrepareLogEvent c => some (cowList c)
  | _ => none

/-- The `EventData` variants without data. -/
def edUnit : binlog.events.EventData → Bool
  | .UnknownEvent | .StopEvent | .SlaveEvent | .HeartbeatEvent => true
  | _ => false

/-- The type codes `read_data` does not parse: the data-less events (`UNKNOWN_EVENT`,
    `STOP_EVENT`, `SLAVE_EVENT`, `HEARTBEAT_EVENT`) and those whose data it keeps raw (the
    pre-5.0 load events, `START_EVENT_V3`, the pre-GA rows events, `IGNORABLE_EVENT`,
    `TRANSACTION_CONTEXT_EVENT`, `VIEW_CHANGE_EVENT`, `XA_PREPARE_LOG_EVENT`). -/
def edUnitCodes : List Nat := [0, 3, 7, 27]

/-- See `edUnitCodes`. -/
def edRawCodes : List Nat := [1, 6, 8, 9, 10, 11, 12, 20, 21, 22, 28, 36, 37, 38]

/-- The type code of each `EventData` variant (for rows events, of the wrapped event's type). -/
def edTypeCode : binlog.events.EventData → Nat
  | .UnknownEvent => 0 | .StartEventV3 _ => 1 | .QueryEvent _ => 2 | .StopEvent => 3
  | .RotateEvent _ => 4 | .IntvarEvent _ => 5 | .LoadEvent _ => 6 | .SlaveEvent => 7
  | .CreateFileEvent _ => 8 | .AppendBlockEvent _ => 9 | .ExecLoadEvent _ => 10
  | .DeleteFileEvent _ => 11 | .NewLoadEvent _ => 12 | .RandEvent _ => 13 | .UserVarEvent _ => 14
  | .FormatDescriptionEvent _ => 15 | .XidEvent _ => 16 | .BeginLoadQueryEvent _ => 17
  | .ExecuteLoadQueryEvent _ => 18 | .TableMapEvent _ => 19 | .PreGaWriteRowsEvent _ => 20
  | .PreGaUpdateRowsEvent _ => 21 | .PreGaDeleteRowsEvent _ => 22 | .IncidentEvent _ => 26
  | .HeartbeatEvent => 27 | .IgnorableEvent _ => 28 | .RowsQueryEvent _ => 29
  | .GtidEvent _ => 33 | .AnonymousGtidEvent _ => 34 | .PreviousGtidsEvent _ => 35
  | .TransactionContextEvent _ => 36 | .ViewChangeEvent _ => 37 | .XaPrepareLogEvent _ => 38
  | .RowsEvent r => eventTypeCode (rowsInner r).event_type
  | .TransactionPayloadEvent _ => 40

end Defs
