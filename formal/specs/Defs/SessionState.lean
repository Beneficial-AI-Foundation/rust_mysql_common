import Defs.CmdPackets

/-!
# Session state tracking (the `session_state_info` of an OK packet)

From the OK packet page
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_ok_packet.html>, "Session
State Information"): `session_state_info` is a sequence of entries, each a `type` (1 byte) and
its `data` (a length-encoded string). The types (`enum_session_state_type`) and the layout of
`data`:

| code | type                                        | `data`                                        |
|------|---------------------------------------------|-----------------------------------------------|
| 0    | `SESSION_TRACK_SYSTEM_VARIABLES`            | name, value (length-encoded strings)          |
| 1    | `SESSION_TRACK_SCHEMA`                      | the schema name (length-encoded string)       |
| 2    | `SESSION_TRACK_STATE_CHANGE`                | `"1"` or `"0"` (length-encoded string)        |
| 3    | `SESSION_TRACK_GTIDS`                       | an encoding specification byte (only `0` is defined), then the GTID set (length-encoded string) |
| 4    | `SESSION_TRACK_TRANSACTION_CHARACTERISTICS` | length-encoded string                          |
| 5    | `SESSION_TRACK_TRANSACTION_STATE`           | length-encoded string                          |

MySQL sends one name/value pair per system-variable entry; the crate's reader accepts several in
one entry.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The protocol code of a session state type. -/
def sessionStateTypeCode : constants.SessionStateType → Nat
  | .SESSION_TRACK_SYSTEM_VARIABLES => 0
  | .SESSION_TRACK_SCHEMA => 1
  | .SESSION_TRACK_STATE_CHANGE => 2
  | .SESSION_TRACK_GTIDS => 3
  | .SESSION_TRACK_TRANSACTION_CHARACTERISTICS => 4
  | .SESSION_TRACK_TRANSACTION_STATE => 5

/-- The session state type with code `n`, if any (codes 0–5). -/
def sessionStateTypeOfCode : Nat → Option constants.SessionStateType
  | 0 => some .SESSION_TRACK_SYSTEM_VARIABLES
  | 1 => some .SESSION_TRACK_SCHEMA
  | 2 => some .SESSION_TRACK_STATE_CHANGE
  | 3 => some .SESSION_TRACK_GTIDS
  | 4 => some .SESSION_TRACK_TRANSACTION_CHARACTERISTICS
  | 5 => some .SESSION_TRACK_TRANSACTION_STATE
  | _ => none

/-- A session state entry, as the specs describe it: its type and its raw `data`. -/
abbrev SsInfo := constants.SessionStateType × List U8

/-- The `SsInfo` of a `SessionStateInfo`. -/
def SsInfo.of (s : packets.SessionStateInfo) : SsInfo := (s.data_type.1, cowList s.data.1)

/-- The protocol's encoding of an entry: the type code, then the data as a length-encoded string. -/
def ssInfoEnc (i : SsInfo) : List U8 := byte (sessionStateTypeCode i.1) :: lenencStr i.2

/-- The crate's reader of an entry (`SessionStateInfo::deserialize`): the type byte (`none` on an
    empty input; `none`, the byte consumed, if it is not a code 0–5), then the data by
    `checkedLenencStr`. -/
def ssInfoRead : List U8 → Option SsInfo × List U8
  | [] => (none, [])
  | t :: rest =>
    match sessionStateTypeOfCode t.val with
    | none => (none, rest)
    | some ty =>
      match checkedLenencStr rest with
      | (some d, rest') => (some (ty, d), rest')
      | (none, rest') => (none, rest')

/-- Entries read one after the other until the input is exhausted, `none` at the first entry
    `ssInfoRead` rejects. (`fuel` bounds the recursion; each entry consumes at least one byte, so
    `fuel = bs.length` suffices, see `ssInfos`.) -/
def ssInfosFuel : Nat → List U8 → Option (List SsInfo)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs =>
    match ssInfoRead bs with
    | (some i, rest) => (ssInfosFuel fuel rest).map (i :: ·)
    | (none, _) => none

/-- The crate's reading of a `session_state_info` string (`OkPacket::session_state_info`): the
    entries until the string is exhausted; `none` if one is malformed. -/
def ssInfos (bs : List U8) : Option (List SsInfo) := ssInfosFuel bs.length bs

/-- A decoded session state change, as the specs describe it (`SessionStateChange`). -/
inductive SsChange where
  | isTracked (b : Bool)
  | schema (s : List U8)
  | systemVariables (vs : List (List U8 × List U8))
  | gtids (s : List U8)
  | trxCharacteristics (s : List U8)
  | trxState (s : List U8)
  | unsupported (s : List U8)

/-- The `SsChange` of a `SessionStateChange`. -/
def SsChange.of : packets.session_state_change.SessionStateChange → SsChange
  | .IsTracked b => .isTracked b
  | .Schema s => .schema (cowList s.1)
  | .SystemVariables vs => .systemVariables (vs.val.map (fun v => (cowList v.«name».1, cowList v.value.1)))
  | .Gtids g => .gtids (cowList g.1)
  | .TransactionCharacteristics t => .trxCharacteristics (cowList t.1)
  | .TransactionState t => .trxState (cowList t.1)
  | .Unsupported u => .unsupported (cowList u.1)

/-- The protocol's `data` of a change (the table above). The crate writes `Unsupported` as a
    length-encoded string, and `IsTracked` as `"1"`/`"0"`. -/
def ssChangeEnc : SsChange → List U8
  | .isTracked b => lenencStr [byte (if b then 49 else 48)]
  | .schema s => lenencStr s
  | .systemVariables vs => vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)
  | .gtids s => byte 0 :: lenencStr s
  | .trxCharacteristics s => lenencStr s
  | .trxState s => lenencStr s
  | .unsupported s => lenencStr s

/-- One name/value pair (`SystemVariable::deserialize`): two length-encoded strings by
    `checkedLenencStr`, stopping at the first failure. -/
def sysVarRead (bs : List U8) : Option (List U8 × List U8) × List U8 :=
  match checkedLenencStr bs with
  | (none, rest) => (none, rest)
  | (some n, rest) =>
    match checkedLenencStr rest with
    | (none, rest') => (none, rest')
    | (some v, rest') => (some (n, v), rest')

/-- Name/value pairs (`sysVarRead`) until the input is exhausted, stopping at the first failure
    (with what that read left of the input). (`fuel` bounds the recursion; `bs.length` suffices,
    as each pair takes at least 2 bytes.) -/
def sysVarsFuel : Nat → List U8 → Option (List (List U8 × List U8)) × List U8
  | _, [] => (some [], [])
  | 0, bs => (none, bs)
  | fuel + 1, bs =>
    match sysVarRead bs with
    | (none, rest) => (none, rest)
    | (some nv, rest) =>
      match sysVarsFuel fuel rest with
      | (some vs, r) => (some (nv :: vs), r)
      | (none, r) => (none, r)

/-- The GTIDs `data` (`Gtids::deserialize`): the encoding byte is skipped unchecked (`none`,
    nothing consumed, on an empty input), then a length-encoded string. -/
def gtidsRead : List U8 → Option (List U8) × List U8
  | [] => (none, [])
  | _ :: rest => checkedLenencStr rest

/-- A length-encoded string read by `checkedLenencStr`, wrapped by `k`. -/
def lenencAs (k : List U8 → SsChange) (bs : List U8) : Option SsChange × List U8 :=
  match checkedLenencStr bs with
  | (some s, rest) => (some (k s), rest)
  | (none, rest) => (none, rest)

/-- The crate's reader of the `data` of a change of type `ty` (`SessionStateChange::
    deserialize`), per the table above, with what it leaves of the input. **Crate behaviour**:
    system variables are read as pairs until the input is exhausted (several per entry);
    `STATE_CHANGE` gives `true` exactly for the string `"1"` (any other well-formed string, `"0"`
    or not, gives `false`; a malformed length-encoded string is an error); the GTID encoding byte is skipped without being checked (`none`, nothing
    consumed, on an empty input); `Unsupported` is never produced. -/
def ssChangeRead (ty : constants.SessionStateType) (bs : List U8) : Option SsChange × List U8 :=
  match ty with
  | .SESSION_TRACK_SYSTEM_VARIABLES =>
    match sysVarsFuel bs.length bs with
    | (some vs, rest) => (some (.systemVariables vs), rest)
    | (none, rest) => (none, rest)
  | .SESSION_TRACK_SCHEMA => lenencAs .schema bs
  | .SESSION_TRACK_STATE_CHANGE => lenencAs (fun s => .isTracked (decide (s = [byte 49]))) bs
  | .SESSION_TRACK_GTIDS =>
    match gtidsRead bs with
    | (some s, rest) => (some (.gtids s), rest)
    | (none, rest) => (none, rest)
  | .SESSION_TRACK_TRANSACTION_CHARACTERISTICS => lenencAs .trxCharacteristics bs
  | .SESSION_TRACK_TRANSACTION_STATE => lenencAs .trxState bs

/-- The type a change is written under (`none` for `unsupported`, which has none). -/
def SsChange.type? : SsChange → Option constants.SessionStateType
  | .isTracked _ => some .SESSION_TRACK_STATE_CHANGE
  | .schema _ => some .SESSION_TRACK_SCHEMA
  | .systemVariables _ => some .SESSION_TRACK_SYSTEM_VARIABLES
  | .gtids _ => some .SESSION_TRACK_GTIDS
  | .trxCharacteristics _ => some .SESSION_TRACK_TRANSACTION_CHARACTERISTICS
  | .trxState _ => some .SESSION_TRACK_TRANSACTION_STATE
  | .unsupported _ => none

end Defs
