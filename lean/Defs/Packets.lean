import Defs.LenEnc
import Defs.Flags

/-!
# Column definitions, OK, EOF and ERR packets

From the protocol pages:

* `Protocol::ColumnDefinition41`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_query_response_text_resultset_column_definition.html>):
  `catalog`, `schema`, `table`, `org_table`, `name`, `org_name` as length-encoded strings; the
  length of the fixed-length fields as a length-encoded integer, always `0x0c`; `character_set`
  (2 bytes); `column_length` (4 bytes); `type` (1 byte); `flags` (2 bytes); `decimals` (1 byte);
  then 2 filler bytes `0x00 0x00` (the `0x0c` counts them; MySQL writes them, the page omits them).
* OK packet (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_ok_packet.html>),
  with `CLIENT_PROTOCOL_41`: header `0x00` (or `0xFE` when it ends a result set), `affected_rows`
  and `last_insert_id` (length-encoded integers), `status_flags` (2 bytes), `warnings` (2 bytes);
  then, with `CLIENT_SESSION_TRACK`, `info` (length-encoded string) and, if the status has
  `SERVER_SESSION_STATE_CHANGED`, `session_state_info` (length-encoded string); without it,
  `info` as the rest of the packet. MySQL's `net_send_ok` (`sql/protocol_classic.cc`) differs:
  with `CLIENT_SESSION_TRACK` it writes `info` only if it is not empty or the session state
  changed; without it, `info` as a length-encoded string, only when it is not empty. The crate
  reads both forms.
* EOF packet (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_eof_packet.html>),
  with `CLIENT_PROTOCOL_41`: header `0xFE`, `warnings` (2 bytes), `status_flags` (2 bytes).
* ERR packet (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_err_packet.html>):
  header `0xFF`, `error_code` (2 bytes); with `CLIENT_PROTOCOL_41`, `sql_state_marker` `#` and
  `sql_state` (5 bytes); `error_message` as the rest of the packet. MariaDB's progress report
  (with `CLIENT_PROGRESS`, error code `0xFFFF`): a byte (number of strings, 1), `stage`,
  `max_stage` (1 byte each), `progress` (3 bytes), `progress_info` (length-encoded string).

All integers are little-endian. The readers below describe the crate's parsers; their docstrings
say where these are stricter or more lenient than the protocol.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- `n` length-encoded strings read one after the other by `checkedLenencStr`, stopping at the
    first failure (with what that read left of the input). -/
def lenencStrs : Nat → List U8 → Option (List (List U8)) × List U8
  | 0, bs => (some [], bs)
  | n + 1, bs =>
    match checkedLenencStr bs with
    | (none, rest) => (none, rest)
    | (some s, rest) =>
      match lenencStrs n rest with
      | (some ss, rest') => (some (s :: ss), rest')
      | (none, rest') => (none, rest')

/-! ## Column definitions -/

/-- A column definition, as the specs describe it. -/
structure ColDef where
  catalog : List U8
  schema : List U8
  table : List U8
  orgTable : List U8
  colName : List U8
  orgName : List U8
  charset : Nat
  length : Nat
  type : constants.ColumnType
  flags : Nat
  decimals : Nat

/-- The six string fields of a column definition's metadata (`ColumnMeta`), in protocol order. -/
def metaFields (m : packets.ColumnMeta) : List (List U8) :=
  [cowList m.catalog.1, cowList m.schema.1, cowList m.table.1, cowList m.org_table.1,
   cowList m.name.1, cowList m.org_name.1]

/-- The `ColDef` of a `Column`. -/
def ColDef.ofColumn (c : packets.Column) : ColDef where
  catalog := cowList c.«meta».catalog.1
  schema := cowList c.«meta».schema.1
  table := cowList c.«meta».table.1
  orgTable := cowList c.«meta».org_table.1
  colName := cowList c.«meta».name.1
  orgName := cowList c.«meta».org_name.1
  charset := c.character_set.1.val
  length := c.column_length.1.val
  type := c.column_type.1
  flags := c.flags.1.val
  decimals := c.decimals.1.val

/-- The protocol's encoding of a column definition (`Protocol::ColumnDefinition41`). -/
def colDefEnc (c : ColDef) : List U8 :=
  lenencStr c.catalog ++ lenencStr c.schema ++ lenencStr c.table ++ lenencStr c.orgTable
    ++ lenencStr c.colName ++ lenencStr c.orgName
    ++ [byte 0x0c] ++ leBytes 2 c.charset ++ leBytes 4 c.length ++ [byte (columnTypeCode c.type)]
    ++ leBytes 2 c.flags ++ [byte c.decimals, byte 0, byte 0]

/-- **What `MySerialize for Column` writes, which is not the protocol layout**: `column_length`
    (4 bytes) comes *before* `character_set` (2 bytes), the reverse of `colDefEnc` and of what the
    crate's own reader expects. Everything else is as in `colDefEnc`. The crate reads it back
    **without an error but with wrong `character_set` and `column_length`**
    (`colDefRead_colDefEncCrate`). -/
def colDefEncCrate (c : ColDef) : List U8 :=
  lenencStr c.catalog ++ lenencStr c.schema ++ lenencStr c.table ++ lenencStr c.orgTable
    ++ lenencStr c.colName ++ lenencStr c.orgName
    ++ [byte 0x0c] ++ leBytes 4 c.length ++ leBytes 2 c.charset ++ [byte (columnTypeCode c.type)]
    ++ leBytes 2 c.flags ++ [byte c.decimals, byte 0, byte 0]

/-- The crate's reader of a column definition: the six strings by `lenencStrs`; then 13 bytes
    (`none`, nothing more consumed, if there are fewer), which are consumed whatever they hold.
    `none` if the first of them is not `0x0c` or the type byte is not a known type code. The flags
    are not checked (every bit is a known flag). **Crate behaviour**: the catalog is not checked
    to be `def`; the filler bytes are skipped without being checked; bytes after the 13 (such as
    MySQL's `default values` of `COM_FIELD_LIST`) are left unread. -/
def colDefRead (bs : List U8) : Option ColDef × List U8 :=
  match lenencStrs 6 bs with
  | (some [c, s, t, ot, n, on], rest) =>
    if rest.length < 13 then (none, rest)
    else
      let f := rest.take 13
      let b (i : Nat) : Nat := (f.getD i (byte 0)).val
      match columnTypeOfCode (b 7) with
      | some ty =>
        (if b 0 = 0x0c then
          some { catalog := c, schema := s, table := t, orgTable := ot, colName := n, orgName := on,
                 charset := b 1 + 256 * b 2, length := leNat ((f.drop 3).take 4), type := ty,
                 flags := b 8 + 256 * b 9, decimals := b 10 }
         else none, rest.drop 13)
      | none => (none, rest.drop 13)
  | (_, rest) => (none, rest)

/-! ## OK and EOF packets -/

/-- The fields of an OK packet as the parsers read them (`OkPacketBody`). -/
structure OkBody where
  affectedRows : Nat
  lastInsertId : Nat
  status : Nat
  warnings : Nat
  info : List U8
  sessionStateInfo : List U8
deriving DecidableEq

/-- The `OkBody` of an `OkPacketBody`. -/
def OkBody.ofBody (b : packets.OkPacketBody) : OkBody :=
  ⟨b.affected_rows.1.val, b.last_insert_id.1.val, b.status_flags.1.val, b.warnings.1.val,
   cowList b.info.1, cowList b.session_state_info.1⟩

/-- An OK packet as the crate presents it (`OkPacket`): a last insert id of 0 and empty strings
    are absent. -/
structure OkPkt where
  affectedRows : Nat
  lastInsertId : Option Nat
  status : Nat
  warnings : Nat
  info : Option (List U8)
  sessionStateInfo : Option (List U8)
deriving DecidableEq

/-- The `OkPkt` of an `OkPacket`. -/
def OkPkt.ofPacket (p : packets.OkPacket) : OkPkt :=
  ⟨p.affected_rows.val, p.last_insert_id.map (·.val), p.status_flags.val, p.warnings.val,
   p.info.map (fun rb => cowList rb.1), p.session_state_info.map (fun rb => cowList rb.1)⟩

/-- The crate's conversion of the fields to an `OkPacket` (`TryFrom<OkPacketBody>`, which never
    fails): a last insert id of 0 becomes `None`, an empty `info` or session state `None`. -/
def OkBody.toPkt (b : OkBody) : OkPkt :=
  ⟨b.affectedRows, if b.lastInsertId = 0 then none else some b.lastInsertId, b.status, b.warnings,
   if b.info = [] then none else some b.info,
   if b.sessionStateInfo = [] then none else some b.sessionStateInfo⟩

/-- Reads a status flag word: `none` if it has a bit the crate does not know (bit 2, value 4, not
    sent by current servers: **crate behaviour**, a robustness quirk rather than a protocol
    violation). -/
def statusRead (n : Nat) : Option Nat := if n &&& statusFlagsAll = n then some n else none

/-- The crate's reader of `status_flags` then `warnings`: `none` with the input unchanged if there
    are fewer than 4 bytes; otherwise the 4 bytes are consumed, and the result is `none` if the
    status has an unknown bit. -/
def okStatusRead (bs : List U8) : Option (Nat × Nat) × List U8 :=
  if bs.length < 4 then (none, bs)
  else ((statusRead (leNat (bs.take 2))).map (fun s => (s, leNat ((bs.drop 2).take 2))), bs.drop 4)

/-- The crate's reader of the end of an OK packet (`info` and `session_state_info`), given the
    capability flags `caps` and the status flags `status`:
    * with `CLIENT_SESSION_TRACK` and input left: `info` as a length-encoded string, then, if the
      status has `SERVER_SESSION_STATE_CHANGED`, the session state as a length-encoded string
      (otherwise empty);
    * otherwise, if the first byte left is not `0`: `info` as a length-encoded string, the session
      state empty;
    * otherwise both empty, nothing consumed.
    Strings are read with `checkedLenencStr` (with its `0xFB`/`0xFF` quirk). **Crate behaviour**:
    bytes left after these fields are not consumed and not checked. -/
def okTailRead (caps status : Nat) (bs : List U8) : Option (List U8 × List U8) × List U8 :=
  if hasFlag caps CLIENT_SESSION_TRACK ∧ bs ≠ [] then
    match checkedLenencStr bs with
    | (none, rest) => (none, rest)
    | (some info, rest) =>
      if hasFlag status SERVER_SESSION_STATE_CHANGED then
        match checkedLenencStr rest with
        | (none, rest') => (none, rest')
        | (some ssi, rest') => (some (info, ssi), rest')
      else (some (info, []), rest)
  else
    match bs with
    | b :: _ =>
      if 0 < b.val then
        match checkedLenencStr bs with
        | (none, rest) => (none, rest)
        | (some info, rest) => (some (info, []), rest)
      else (some ([], []), bs)
    | [] => (some ([], []), [])

/-- The crate's reader of an OK packet body after the header (`CommonOkPacket::parse_body`), with
    capability flags `caps`: `affected_rows` and `last_insert_id` by `checkedLenencInt`, then
    `okStatusRead`, then `okTailRead`, stopping at the first failure. **Crate behaviour**:
    `CLIENT_PROTOCOL_41` is assumed whatever `caps` says. -/
def okBodyRead (caps : Nat) (bs : List U8) : Option OkBody × List U8 :=
  match checkedLenencInt bs with
  | (none, rest) => (none, rest)
  | (some ar, rest) =>
    match checkedLenencInt rest with
    | (none, rest) => (none, rest)
    | (some li, rest) =>
      match okStatusRead rest with
      | (none, rest) => (none, rest)
      | (some (s, w), rest) =>
        match okTailRead caps s rest with
        | (none, rest) => (none, rest)
        | (some (i, ssi), rest) => (some ⟨ar, li, s, w, i, ssi⟩, rest)

/-- The crate's reader of the body of an OK packet that ends a result set
    (`ResultSetTerminator::parse_body`): as `okBodyRead`, but the affected rows and last insert id
    are read (and must be well formed) and then reported as 0. -/
def rsTerminatorBodyRead (caps : Nat) (bs : List U8) : Option OkBody × List U8 :=
  match okBodyRead caps bs with
  | (some b, rest) => (some { b with affectedRows := 0, lastInsertId := 0 }, rest)
  | (none, rest) => (none, rest)

/-- The crate's reader of an EOF packet body after the header (`OldEofPacket::parse_body`):
    `warnings` then `status_flags`, as `okStatusRead` but in that order; the other fields are 0 or
    empty. **Crate behaviour**: `CLIENT_PROTOCOL_41` is assumed; bytes after the 4 are left
    unread. -/
def eofBodyRead (bs : List U8) : Option OkBody × List U8 :=
  if bs.length < 4 then (none, bs)
  else ((statusRead (leNat ((bs.drop 2).take 2))).map (fun s => ⟨0, 0, s, leNat (bs.take 2), [], []⟩),
    bs.drop 4)

/-- The four kinds of OK packet the crate parses (`OkPacketKind` impls). -/
inductive OkKind where
  | resultSetTerminator
  | oldEof
  | networkStreamTerminator
  | commonOk
deriving DecidableEq

/-- The header byte of each kind: `0x00` for an ordinary OK packet, `0xFE` for the others. -/
def OkKind.header : OkKind → Nat
  | .commonOk => 0x00
  | _ => 0xFE

/-- The body reader of each kind. -/
def OkKind.bodyRead (caps : Nat) : OkKind → List U8 → Option OkBody × List U8
  | .resultSetTerminator => rsTerminatorBodyRead caps
  | .oldEof | .networkStreamTerminator => eofBodyRead
  | .commonOk => okBodyRead caps

/-- The crate's reader of an OK packet of kind `k` (`OkPacketDeserializer<k>`): the header byte
    (`none` on an empty input, nothing consumed; `none` if it is not `k.header`, the byte
    consumed), then the body, converted by `OkBody.toPkt`. -/
def okPacketRead (k : OkKind) (caps : Nat) : List U8 → Option OkPkt × List U8
  | [] => (none, [])
  | h :: rest =>
    if h.val ≠ k.header then (none, rest)
    else match k.bodyRead caps rest with
      | (some b, rest') => (some b.toPkt, rest')
      | (none, rest') => (none, rest')

/-- An OK packet with header byte `header`, with `CLIENT_PROTOCOL_41`. With
    `CLIENT_SESSION_TRACK` in `caps`: `info` as a length-encoded string, then the session state if
    the status has `SERVER_SESSION_STATE_CHANGED`; with `compact` (MySQL's `net_send_ok`) `info` is
    left out when it is empty and the status lacks `SERVER_SESSION_STATE_CHANGED`, without
    `compact` (the protocol page) it is always there. Without `CLIENT_SESSION_TRACK`: `info` as a
    length-encoded string if it is not empty (as `net_send_ok`; the page's `string<EOF>` is not what
    servers send nor what the crate reads). -/
def okPacketEnc (header caps : Nat) (compact : Bool) (b : OkBody) : List U8 :=
  byte header :: lenencInt b.affectedRows ++ lenencInt b.lastInsertId ++ leBytes 2 b.status
    ++ leBytes 2 b.warnings
    ++ (if hasFlag caps CLIENT_SESSION_TRACK then
          (if compact ∧ b.info = [] ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED = false then []
           else lenencStr b.info)
            ++ (if hasFlag b.status SERVER_SESSION_STATE_CHANGED then lenencStr b.sessionStateInfo else [])
        else if b.info = [] then [] else lenencStr b.info)

/-- An EOF packet with `CLIENT_PROTOCOL_41`. -/
def eofPacketEnc (warnings status : Nat) : List U8 :=
  byte 0xFE :: leBytes 2 warnings ++ leBytes 2 status

/-! ## ERR packets -/

/-- A progress report, as the specs describe it. -/
structure Progress where
  stage : Nat
  maxStage : Nat
  progress : Nat
  info : List U8
deriving DecidableEq

/-- The `Progress` of a `ProgressReport`. -/
def Progress.of (p : packets.ProgressReport) : Progress :=
  ⟨p.stage.1.val, p.max_stage.1.val, p.progress.1.val, cowList p.stage_info.1⟩

/-- An ERR packet, as the specs describe it: an error (code, SQL state if present, message) or a
    progress report. -/
inductive ErrPkt where
  | error (code : Nat) (state : Option (List U8)) (msg : List U8)
  | progress (p : Progress)
deriving DecidableEq

/-- The `ErrPkt.error` of a `ServerError`. -/
def ErrPkt.ofServerError (e : packets.ServerError) : ErrPkt :=
  .error e.code.1.val (e.state.map (fun s => s.state.val)) (cowList e.message.1)

/-- The `ErrPkt` of an `ErrPacket`. -/
def ErrPkt.of : packets.ErrPacket → ErrPkt
  | .Error e => .ofServerError e
  | .Progress p => .progress (.of p)

/-- A progress report after the error code (MariaDB): number of strings 1, stage, max stage,
    progress (3 bytes), stage info (length-encoded). -/
def progressEnc (p : Progress) : List U8 :=
  byte 1 :: byte p.stage :: byte p.maxStage :: leBytes 3 p.progress ++ lenencStr p.info

/-- The protocol's ERR packet: `0xFF`, the error code (`0xFFFF` for a progress report), then the
    SQL state (marker `#` and the 5 state bytes) if present and the message, or the progress
    report. -/
def errPacketEnc : ErrPkt → List U8
  | .error code state msg =>
    byte 0xFF :: leBytes 2 code ++ (match state with | some s => byte 0x23 :: s | none => []) ++ msg
  | .progress p => byte 0xFF :: leBytes 2 0xFFFF ++ progressEnc p

/-- The crate's reader of a SQL state (`SqlState::deserialize`): the marker byte (`none` on an
    empty input; `none` if it is not `#`, the byte consumed), then 5 bytes (`none`, only the marker
    consumed, if there are fewer). -/
def sqlStateRead : List U8 → Option (List U8) × List U8
  | [] => (none, [])
  | m :: rest =>
    if m.val ≠ 0x23 then (none, rest)
    else if rest.length < 5 then (none, rest)
    else (some (rest.take 5), rest.drop 5)

/-- The crate's reader of a progress report (`ProgressReport::deserialize`): 6 bytes (`none`,
    nothing consumed, if fewer) whose first byte (the number of strings) is ignored, then the stage
    info by `checkedLenencStr`. -/
def progressRead (bs : List U8) : Option Progress × List U8 :=
  if bs.length < 6 then (none, bs)
  else
    let b (i : Nat) : Nat := (bs.getD i (byte 0)).val
    match checkedLenencStr (bs.drop 6) with
    | (some info, rest) => (some ⟨b 1, b 2, leNat ((bs.drop 3).take 3), info⟩, rest)
    | (none, rest) => (none, rest)

/-- The crate's reader of the rest of an error packet after the error code `code`
    (`ServerError::deserialize`): with `CLIENT_PROTOCOL_41` (`p41`), the SQL state, 6 bytes (`none`,
    nothing consumed, if fewer; `none`, the 6 consumed, if the marker is not `#`); the message is
    the rest of the input. **Crate behaviour**: with `CLIENT_PROTOCOL_41` the marker is required
    (MySQL's client accepts a message without it). -/
def serverErrorRead (code : Nat) (p41 : Bool) (bs : List U8) : Option ErrPkt × List U8 :=
  if p41 then
    if bs.length < 6 then (none, bs)
    else if (bs.getD 0 (byte 0)).val ≠ 0x23 then (none, bs.drop 6)
    else (some (.error code (some ((bs.drop 1).take 5)) (bs.drop 6)), [])
  else (some (.error code none bs), [])

/-- The crate's reader of an ERR packet (`ErrPacket::deserialize`) with capability flags `caps`:
    3 bytes (`none`, nothing consumed, if fewer), consumed whatever they hold: `none` if the first
    is not `0xFF`; the next two are the error code. With `CLIENT_PROGRESS_OBSOLETE` and code
    `0xFFFF`, a progress report (`progressRead`); otherwise `serverErrorRead`, with
    `CLIENT_PROTOCOL_41` from `caps`. -/
def errPacketRead (caps : Nat) (bs : List U8) : Option ErrPkt × List U8 :=
  if bs.length < 3 then (none, bs)
  else
    let code := leNat ((bs.drop 1).take 2)
    let rest := bs.drop 3
    if (bs.getD 0 (byte 0)).val ≠ 0xFF then (none, rest)
    else if code = 0xFFFF ∧ hasFlag caps CLIENT_PROGRESS_OBSOLETE then
      match progressRead rest with
      | (some p, rest') => (some (.progress p), rest')
      | (none, rest') => (none, rest')
    else serverErrorRead code (hasFlag caps CLIENT_PROTOCOL_41) rest

/-- When an ERR packet is read back as it was written, given the capability flags `caps`: an
    error's SQL state is present iff `CLIENT_PROTOCOL_41`, and its code is not `0xFFFF` if
    `CLIENT_PROGRESS_OBSOLETE` (that code then means a progress report); a progress report needs
    `CLIENT_PROGRESS_OBSOLETE` and a progress below `2^24` (it is sent in 3 bytes). -/
def errCompatible (caps : Nat) : ErrPkt → Prop
  | .error code state _ =>
    (state.isSome ↔ hasFlag caps CLIENT_PROTOCOL_41) ∧
      (code ≠ 0xFFFF ∨ hasFlag caps CLIENT_PROGRESS_OBSOLETE = false)
  | .progress p => hasFlag caps CLIENT_PROGRESS_OBSOLETE ∧ p.progress < 2 ^ 24

end Defs
