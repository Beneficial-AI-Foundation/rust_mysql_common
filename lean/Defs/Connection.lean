import Defs.Packets
import Defs.Convert

/-!
# Connection-phase packets

From the protocol pages of the connection phase
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_connection_phase.html>) and
its sub-pages. All integers are little-endian; `string<NUL>` is the bytes followed by `0x00`,
`string<EOF>` the rest of the packet, `string<lenenc>` a length-encoded string.

* `Protocol::HandshakeV10` (server → client): `protocol_version` (1, `10`), `server_version`
  `string<NUL>`, `thread_id` (4), `auth_plugin_data_part_1` (8), filler `0x00`,
  `capability_flags_1` (the lower 2 bytes), `character_set` (1), `status_flags` (2),
  `capability_flags_2` (the upper 2 bytes), `auth_plugin_data_len` (1; `0` without
  `CLIENT_PLUGIN_AUTH`), 10 reserved zero bytes (MariaDB sends its extended capabilities in the
  last 4), then, with `CLIENT_SECURE_CONNECTION`, `auth_plugin_data_part_2` of
  `max(13, auth_plugin_data_len - 8)` bytes (MySQL: 12 bytes and a `0x00`) and, with
  `CLIENT_PLUGIN_AUTH`, `auth_plugin_name` `string<NUL>` (some MySQL versions omit the `0x00`).
* `Protocol::HandshakeResponse41` (client → server): `client_flag` (4), `max_packet_size` (4),
  `character_set` (1), 23 filler zero bytes (MariaDB: 19, then its extended capabilities (4)),
  `username` `string<NUL>`, the auth response (with `CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA`
  `string<lenenc>`; else, with `CLIENT_SECURE_CONNECTION`, a 1-byte length and the bytes; else
  `string<NUL>`), with `CLIENT_CONNECT_WITH_DB` `database` `string<NUL>`, with
  `CLIENT_PLUGIN_AUTH` `client_plugin_name` `string<NUL>`, with `CLIENT_CONNECT_ATTRS` the
  length (lenenc) of the attributes and then each key and value as `string<lenenc>`.
* `Protocol::SSLRequest`: the first 32 bytes of a `HandshakeResponse41`.
* `Protocol::AuthSwitchRequest`: `0xFE`, `plugin_name` `string<NUL>`, `auth_plugin_data`
  `string<EOF>`. `Protocol::OldAuthSwitchRequest`: `0xFE` alone.
* `Protocol::AuthMoreData`: `0x01`, `string<EOF>` (also the crate's `PublicKeyResponse`: `0x01`
  and the server's PEM key); the `caching_sha2_password` public key request is `0x02`.
* `COM_CHANGE_USER`: `0x11`, `user` `string<NUL>`, the auth response (with
  `CLIENT_SECURE_CONNECTION` a 1-byte length and the bytes, else `string<NUL>`), `database`
  `string<NUL>`, then, if there is more data, `character_set` (2), with `CLIENT_PLUGIN_AUTH` the
  plugin name `string<NUL>`, with `CLIENT_CONNECT_ATTRS` the attributes as above.
* `LOCAL INFILE` request (`page_protocol_com_query_response_local_infile_request.html`):
  `0xFB`, `filename` `string<EOF>`.

The readers below describe the crate's parsers (with what each leaves of the input); their
docstrings say where they deviate from the protocol. The encoders are the protocol layouts, as
the crate fills them from its fields.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Capability flags (`CLIENT_*`) -/

/-- `CLIENT_CONNECT_WITH_DB` (bit 3). -/
def CLIENT_CONNECT_WITH_DB : Nat := 2 ^ 3

/-- `CLIENT_SECURE_CONNECTION` (bit 15; `CLIENT_RESERVED2` in current MySQL). -/
def CLIENT_SECURE_CONNECTION : Nat := 2 ^ 15

/-- `CLIENT_PLUGIN_AUTH` (bit 19). -/
def CLIENT_PLUGIN_AUTH : Nat := 2 ^ 19

/-- `CLIENT_CONNECT_ATTRS` (bit 20). -/
def CLIENT_CONNECT_ATTRS : Nat := 2 ^ 20

/-- `CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA` (bit 21). -/
def CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA : Nat := 2 ^ 21

/-- The MariaDB extended capability bits the crate knows (`MARIADB_CLIENT_PROGRESS` (1) to
    `MARIADB_CLIENT_BULK_UNIT_RESULTS` (32)): `from_bits_truncate` keeps exactly these. -/
def mariadbCapabilitiesAll : Nat := 63

/-- The 32-bit flag word `x` with the bits of `bit` set (`on`) or cleared
    (`CapabilityFlags::insert` / `remove`). -/
def setFlag (x bit : Nat) (on : Bool) : Nat := if on then x ||| bit else andNot 32 x bit

/-! ## Byte strings -/

/-- No byte of `bs` is `0`. -/
def NoNul (bs : List U8) : Prop := ∀ b ∈ bs, b.val ≠ 0

/-- Whether `bs` has a `0` byte. -/
def hasNul (bs : List U8) : Bool := bs.any (fun b => b.val == 0)

/-- `bs` without its last byte if that byte is `0` (otherwise `bs`). -/
def dropTrailingNul (bs : List U8) : List U8 :=
  match bs.getLast? with
  | some b => if b.val = 0 then bs.dropLast else bs
  | none => bs

/-- The crate's reader of a `string<NUL>` (`RawBytes<NullBytes>`): the bytes before the first `0`,
    consuming the `0`; `none`, nothing consumed, if there is no `0`. -/
def nulStrRead (bs : List U8) : Option (List U8) × List U8 :=
  if hasNul bs then (some (beforeZero bs), bs.drop ((beforeZero bs).length + 1)) else (none, bs)

/-- A `string<NUL>` as the crate writes one (`NullBytes::serialize`): the bytes up to the first `0`
    (all of them if there is none), then `0`. -/
def nulStr (bs : List U8) : List U8 := beforeZero bs ++ [byte 0]

/-! ## Authentication plugins -/

/-- The name of an authentication plugin, from the MySQL and MariaDB plugin documentation (what
    `AuthPlugin::as_bytes` should return); `Other` carries its name. -/
def authPluginName : packets.AuthPlugin → List U8
  | .MysqlOldPassword => utf8 "mysql_old_password"
  | .MysqlClearPassword => utf8 "mysql_clear_password"
  | .MysqlNativePassword => utf8 "mysql_native_password"
  | .Sha256Password => utf8 "sha256_password"
  | .CachingSha2Password => utf8 "caching_sha2_password"
  | .Ed25519 => utf8 "client_ed25519"
  | .Parsec => utf8 "parsec"
  | .Other c => cowList c

/-- The plugins the crate knows by name. -/
def knownPlugins : List packets.AuthPlugin :=
  [.MysqlOldPassword, .MysqlClearPassword, .MysqlNativePassword, .Sha256Password,
   .CachingSha2Password, .Ed25519, .Parsec]

/-- The known plugin named `n`, if any. -/
def knownPlugin (n : List U8) : Option packets.AuthPlugin :=
  knownPlugins.find? (fun p => decide (authPluginName p = n))

/-- `r` is the plugin named `n`: the known plugin of that name, or else `Other` holding `n`. -/
def IsPluginNamed (n : List U8) (r : packets.AuthPlugin) : Prop :=
  match knownPlugin n with
  | some p => r = p
  | none => ∃ c, r = .Other c ∧ cowList c = n

/-- `r` is in normal form: it is not `Other` with the name of a known plugin. Every plugin the
    crate parses is. -/
def PluginCanonical (r : packets.AuthPlugin) : Prop := IsPluginNamed (authPluginName r) r

/-- What `AuthPlugin::from_bytes(nm)` returns: the plugin named `nm` without one trailing `0`,
    an `Other` borrowing those bytes if no known plugin has that name. -/
def PluginFromBytes (nm : List U8) (r : packets.AuthPlugin) : Prop :=
  match knownPlugin (dropTrailingNul nm) with
  | some p => r = p
  | none => ∃ s : Slice U8, r = .Other (.Borrowed s) ∧ s.val = dropTrailingNul nm

/-- Whether a plugin is `Other`. -/
def isOtherPlugin : packets.AuthPlugin → Bool
  | .Other _ => true
  | _ => false

/-- The plugins whose scramble MySQL sends as a C string, with a trailing `0`
    (`mysql_native_password`, `caching_sha2_password`, `sha256_password`, `mysql_old_password`):
    `AuthSwitchRequest::plugin_data` removes that `0`. -/
def usesCStringScramble (nm : List U8) : Bool :=
  match knownPlugin (dropTrailingNul nm) with
  | some .MysqlNativePassword | some .CachingSha2Password | some .Sha256Password
  | some .MysqlOldPassword => true
  | _ => false

/-! ## Strings and options -/

/-- What `String::from_utf8_lossy(bs)` returns (through `RawBytes::as_str`): the bytes themselves,
    borrowed, if they are valid UTF-8; otherwise an owned string (with `U+FFFD` replacements; the
    trusted model leaves it opaque). -/
def LossyUtf8 (bs : List U8) (c : alloc.borrow.Cow Str String) : Prop :=
  (IsUtf8 bs → ∃ s : Slice U8, c = .Borrowed s ∧ s.val = bs) ∧ (¬ IsUtf8 bs → ∃ t, c = .Owned t)

/-- Two options agree under `R`: both absent, or both present and related. -/
def optMatch {A B : Type} (R : A → B → Prop) : Option A → Option B → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

/-! ## Header-only and `string<EOF>` packets -/

/-- The crate's reader of a packet that is the header byte `h` followed by a `string<EOF>`: the
    payload, consuming everything; `none` on an empty input; `none`, the byte consumed, if the
    first byte is not `h`. -/
def eofPayloadRead (h : Nat) : List U8 → Option (List U8) × List U8
  | [] => (none, [])
  | b :: rest => if b.val = h then (some rest, []) else (none, rest)

/-- The crate's reader of a packet that is just the header byte `h`: `some ()` iff the first byte
    is `h`, consuming only it; `none`, nothing consumed, on an empty input. Bytes after the header
    are left unread. -/
def headerRead (h : Nat) : List U8 → Option Unit × List U8
  | [] => (none, [])
  | b :: rest => (if b.val = h then some () else none, rest)

/-! ## `Protocol::AuthSwitchRequest` -/

/-- The crate's reader of an auth switch request: the header `0xFE` (as `eofPayloadRead`), the
    plugin name by `nulStrRead` (`none` if there is no `0`), the plugin data as the rest. -/
def authSwitchRead : List U8 → Option (List U8 × List U8) × List U8
  | [] => (none, [])
  | b :: rest =>
    if b.val ≠ 0xFE then (none, rest)
    else match nulStrRead rest with
      | (none, r) => (none, r)
      | (some n, r) => (some (n, r), [])

/-- An auth switch request. -/
def authSwitchEnc (nm data : List U8) : List U8 := byte 0xFE :: nulStr nm ++ data

/-! ## `parse_parsec_salt` -/

/-- MariaDB's `parsec` ext-salt (the server's reply after the client's empty first response):
    algorithm `'P'`, an iteration factor, an 18-byte salt; the crate accepts exactly 20 bytes
    with a factor of at most 20 (its practical limit). -/
def parsecSaltOk (data : List U8) : Bool :=
  data.length == 20 && (data.getD 0 (byte 0)).val == 0x50 && (data.getD 1 (byte 0)).val ≤ 20

/-! ## `Protocol::HandshakeV10` -/

/-- A handshake packet's fields, as the specs describe them. `capsLower` and `capsUpper` are the
    two halves of the capability flags as the crate stores them (`capsUpper` already shifted:
    a multiple of `2^16`); `authDataLen` is the `auth_plugin_data_len` byte as stored. -/
structure Handshake where
  protocolVersion : Nat
  serverVersion : List U8
  connectionId : Nat
  scramble1 : List U8
  capsLower : Nat
  collation : Nat
  status : Nat
  capsUpper : Nat
  authDataLen : Nat
  mariadbCaps : Nat
  scramble2 : Option (List U8)
  pluginName : Option (List U8)
deriving DecidableEq

/-- The `Handshake` of a `HandshakePacket`. -/
def Handshake.of (p : packets.HandshakePacket) : Handshake where
  protocolVersion := p.protocol_version.1.val
  serverVersion := cowList p.server_version.1
  connectionId := p.connection_id.1.val
  scramble1 := p.scramble_1.val
  capsLower := p.capabilities_1.1.val
  collation := p.default_collation.1.val
  status := p.status_flags.1.val
  capsUpper := p.capabilities_2.1.val
  authDataLen := p.auth_plugin_data_len.1.val
  mariadbCaps := p.mariadb_ext_capabilities.1.val
  scramble2 := p.scramble_2.map (fun rb => cowList rb.1)
  pluginName := p.auth_plugin_name.map (fun rb => cowList rb.1)

/-- The protocol's length of `auth_plugin_data_part_2` for the length byte `b`: `max(13, b - 8)`. -/
def scramble2Len (b : Nat) : Nat := max 13 (b - 8)

/-- **The crate's length of `auth_plugin_data_part_2`** (`max(13, (b as i8) - 8)`): as
    `scramble2Len` for `b < 128`; **13 for `b ≥ 136`** (the byte is read as a negative `i8`;
    the protocol says `b - 8 ≥ 128`). For `128 ≤ b < 136` the `i8` subtraction overflows: a panic
    (`handshakePanics`; a wrapped value in release builds). -/
def scramble2LenCrate (b : Nat) : Nat := if b < 128 then max 13 (b - 8) else 13

/-- The crate's reader of a handshake packet (`MyDeserialize for HandshakePacket`), when it does
    not panic (`handshakePanics`):
    * the protocol version byte (`none` on an empty input); the server version by `nulStrRead`;
    * 31 bytes (`none`, nothing more consumed, if fewer), consumed whatever they hold:
      connection id (4), `scramble1` (8), the filler (not checked), the lower capability half
      (2), the collation (1), the status (2), the upper capability half (2, shifted by 16), the
      length byte (1), 6 reserved bytes (not checked), MariaDB's capabilities (4, only the known
      bits kept); `none` if the status has a bit the crate does not know (`statusRead`);
    * with `CLIENT_SECURE_CONNECTION` in the lower half, `scramble2LenCrate` bytes of scramble
      (`none`, nothing more consumed, if fewer);
    * with `CLIENT_PLUGIN_AUTH` in the upper half, the plugin name as **all the rest**, without
      one trailing `0` if there is one (the crate tolerates MySQL's missing `0`; bytes after the
      `0` would be part of the name).
    **Crate behaviour**: the protocol version is not checked to be 10; without
    `CLIENT_PLUGIN_AUTH` the bytes after the scramble are left unread; capability bits are not
    checked (all 32 are known). -/
def handshakeRead : List U8 → Option Handshake × List U8
  | [] => (none, [])
  | pv :: r1 =>
    match nulStrRead r1 with
    | (none, r) => (none, r)
    | (some sv, r2) =>
      if r2.length < 31 then (none, r2)
      else
        let f := r2.take 31
        let r3 := r2.drop 31
        let field (i k : Nat) : Nat := leNat ((f.drop i).take k)
        let capsLower := field 13 2
        let status := field 16 2
        let capsUpper := field 18 2 * 2 ^ 16
        let len := field 20 1
        if statusRead status = none then (none, r3)
        else
          let s2 : Option (Option (List U8)) × List U8 :=
            if hasFlag capsLower CLIENT_SECURE_CONNECTION then
              let n := scramble2LenCrate len
              if r3.length < n then (none, r3) else (some (some (r3.take n)), r3.drop n)
            else (some none, r3)
          match s2 with
          | (none, r) => (none, r)
          | (some s2, r4) =>
            let pn : Option (List U8) × List U8 :=
              if hasFlag capsUpper CLIENT_PLUGIN_AUTH then (some (dropTrailingNul r4), [])
              else (none, r4)
            (some { protocolVersion := pv.val, serverVersion := sv, connectionId := field 0 4,
                    scramble1 := (f.drop 4).take 8, capsLower := capsLower,
                    collation := field 15 1, status := status, capsUpper := capsUpper,
                    authDataLen := len, mariadbCaps := field 27 4 &&& mariadbCapabilitiesAll,
                    scramble2 := s2, pluginName := pn.1 }, pn.2)

/-- When the crate's handshake reader panics: the input gets as far as the scramble (a version
    byte, a `0`-terminated server version, 31 more bytes with a known status) with
    `CLIENT_SECURE_CONNECTION` set and a length byte in `128..135`, where `(b as i8) - 8`
    overflows. **A bug**: the length byte is server-controlled. -/
def handshakePanics : List U8 → Prop
  | [] => False
  | _ :: r1 =>
    match nulStrRead r1 with
    | (none, _) => False
    | (some _, r2) =>
      31 ≤ r2.length ∧ statusRead (leNat ((r2.drop 16).take 2)) ≠ none ∧
        hasFlag (leNat ((r2.drop 13).take 2)) CLIENT_SECURE_CONNECTION = true ∧
        128 ≤ (r2.getD 20 (byte 0)).val ∧ (r2.getD 20 (byte 0)).val < 136

/-- The `auth_plugin_data_len` byte the crate writes: `8 + |scramble2|` (at most 247 scramble
    bytes are written) with `CLIENT_PLUGIN_AUTH` and a scramble, else `0` (as the protocol says
    for a server without `CLIENT_PLUGIN_AUTH`). -/
def handshakeLenByte (h : Handshake) : Nat :=
  if hasFlag h.capsUpper CLIENT_PLUGIN_AUTH then
    match h.scramble2 with
    | some s => min s.length 247 + 8
    | none => 0
  else 0

/-- `Protocol::HandshakeV10` with the fields of `h`, as the crate writes it: the reserved bytes
    are 6 zeros and MariaDB's capabilities; the length byte is `handshakeLenByte h` (the stored
    `authDataLen` is not used); the scramble (at most its first 247 bytes) and the plugin name
    (`string<NUL>`) are written when present, **whatever the capability flags say**. The server
    version and the plugin name are cut at their first `0` (`nulStr`). -/
def handshakeEnc (h : Handshake) : List U8 :=
  byte h.protocolVersion :: nulStr h.serverVersion ++ leBytes 4 h.connectionId ++ h.scramble1
    ++ [byte 0] ++ leBytes 2 h.capsLower ++ [byte h.collation] ++ leBytes 2 h.status
    ++ leBytes 2 (h.capsUpper / 2 ^ 16) ++ [byte (handshakeLenByte h)]
    ++ List.replicate 6 (byte 0) ++ leBytes 4 h.mariadbCaps
    ++ (match h.scramble2 with | some s => s.take 247 | none => [])
    ++ (match h.pluginName with | some n => nulStr n | none => [])

/-- When a handshake written by `handshakeEnc` reads back as itself (up to the length byte):
    every field fits, the server version and plugin name have no `0`, the status and MariaDB
    capabilities have only known bits, a scramble is present iff `CLIENT_SECURE_CONNECTION`, and
    has the length the reader will compute from the written length byte (13 to 119 bytes with
    `CLIENT_PLUGIN_AUTH`, so that `8 + n < 128`; exactly 13 without, where the byte is 0), and a
    plugin name is present iff `CLIENT_PLUGIN_AUTH`. -/
def Handshake.Compatible (h : Handshake) : Prop :=
  h.protocolVersion < 256 ∧ NoNul h.serverVersion ∧ h.connectionId < 2 ^ 32 ∧
    h.scramble1.length = 8 ∧ h.capsLower < 2 ^ 16 ∧ h.collation < 256 ∧ h.status < 2 ^ 16 ∧
    statusRead h.status = some h.status ∧ h.capsUpper % 2 ^ 16 = 0 ∧ h.capsUpper < 2 ^ 32 ∧
    h.mariadbCaps &&& mariadbCapabilitiesAll = h.mariadbCaps ∧
    (h.scramble2.isSome = hasFlag h.capsLower CLIENT_SECURE_CONNECTION) ∧
    (∀ s, h.scramble2 = some s →
      if hasFlag h.capsUpper CLIENT_PLUGIN_AUTH then 13 ≤ s.length ∧ s.length ≤ 119
      else s.length = 13) ∧
    (h.pluginName.isSome = hasFlag h.capsUpper CLIENT_PLUGIN_AUTH) ∧
    (∀ n, h.pluginName = some n → NoNul n)

/-- The auth plugin nonce: `scramble1` followed by `scramble2` without its trailing `0` (MySQL's
    20 bytes); the crate right-pads a shorter result with zeros to 20 bytes. -/
def handshakeNonce (scramble1 : List U8) (scramble2 : Option (List U8)) : List U8 :=
  let n := scramble1 ++ (match scramble2 with | some s => dropTrailingNul s | none => [])
  n ++ List.replicate (20 - n.length) (byte 0)

/-! ## Server version strings -/

/-- The maximal run of ASCII digits at the front of `bs`. -/
def digitRun (bs : List U8) : List U8 := bs.takeWhile isDigit

/-- `bs` starts with the byte `c`. -/
def startsWithByte (c : Nat) (bs : List U8) : Bool := (bs.head?.map (·.val)) == some c

/-- `(\d{1,2})\.(\d{1,2})\.` at the front of `bs`, on ASCII input (`\d` an ASCII digit): the two
    groups and the rest. With backtracking, a group is a maximal digit run of 1 or 2 digits
    followed by `.`. -/
def twoVersionGroups (bs : List U8) : Option (List U8 × List U8 × List U8) :=
  let g1 := digitRun bs
  let r1 := bs.drop g1.length
  if 1 ≤ g1.length ∧ g1.length ≤ 2 ∧ startsWithByte 46 r1 then
    let g2 := digitRun (r1.drop 1)
    let r2 := (r1.drop 1).drop g2.length
    if 1 ≤ g2.length ∧ g2.length ≤ 2 ∧ startsWithByte 46 r2 then some (g1, g2, r2.drop 1)
    else none
  else none

/-- What the regex `^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)` (`VERSION_RE`, "the first
    `\d+.\d+.\d+` of a server version") captures in groups 1–3 of ASCII input: two version
    groups, then the first 1–3 digits of the next digit run. -/
def versionReMatch (bs : List U8) : Option (List U8 × List U8 × List U8) :=
  match twoVersionGroups bs with
  | some (g1, g2, r) =>
    let g3 := digitRun r
    if 1 ≤ g3.length then some (g1, g2, g3.take 3) else none
  | none => none

/-- `(\d{1,3})(?:-\d+)?-MariaDB` at the front of `bs` (ASCII): the group (a maximal digit run of
    1–3 digits), followed by `-MariaDB` or by `-`, a digit run and `-MariaDB`. -/
def mariadbTail (bs : List U8) : Option (List U8) :=
  let g3 := digitRun bs
  let r := bs.drop g3.length
  let tag := utf8 "-MariaDB"
  if 1 ≤ g3.length ∧ g3.length ≤ 3 ∧
      (r.take tag.length = tag ∨
        (startsWithByte 45 r ∧ 1 ≤ (digitRun (r.drop 1)).length ∧
          ((r.drop 1).drop (digitRun (r.drop 1)).length).take tag.length = tag))
  then some g3 else none

/-- The match of `(\d{1,2})\.(\d{1,2})\.(\d{1,3})(?:-\d+)?-MariaDB` at the front of `bs`. -/
def mariadbCore (bs : List U8) : Option (List U8 × List U8 × List U8) :=
  match twoVersionGroups bs with
  | some (g1, g2, r) => (mariadbTail r).map (fun g3 => (g1, g2, g3))
  | none => none

/-- What the regex `^(?:5.5.5-)?(\d{1,2})\.(\d{1,2})\.(\d{1,3})(?:-\d+)?-MariaDB`
    (`MARIADB_VERSION_RE`) captures in groups 1–3 of ASCII input. The optional prefix is tried
    first (leftmost-first semantics); its unescaped `.` matches any byte but `\n` (so
    `5x5y5-` is accepted too, a harmless quirk). MariaDB before 11 sends `5.5.5-` before its
    version for old clients. -/
def mariadbVersionReMatch (bs : List U8) : Option (List U8 × List U8 × List U8) :=
  let pre := bs.take 6
  let prefixOk : Bool := pre.length = 6 &&
    (pre.getD 0 (byte 0)).val == 53 && (pre.getD 1 (byte 0)).val != 10 &&
    (pre.getD 2 (byte 0)).val == 53 && (pre.getD 3 (byte 0)).val != 10 &&
    (pre.getD 4 (byte 0)).val == 53 && (pre.getD 5 (byte 0)).val == 45
  match (if prefixOk then mariadbCore (bs.drop 6) else none) with
  | some g => some g
  | none => mariadbCore bs

/-- The bytes of three captured slices. -/
def capturesVal (c : Option (Slice U8 × Slice U8 × Slice U8)) :
    Option (List U8 × List U8 × List U8) :=
  c.map (fun t => (t.1.val, t.2.1.val, t.2.2.val))

/-- A version triple's numbers. -/
def versionVal (r : Option (U16 × U16 × U16)) : Option (Nat × Nat × Nat) :=
  r.map (fun t => (t.1.val, t.2.1.val, t.2.2.val))

/-- The numbers of three ASCII digit strings. -/
def digitsTriple (g : Option (List U8 × List U8 × List U8)) : Option (Nat × Nat × Nat) :=
  g.map (fun t => (digitsVal t.1, digitsVal t.2.1, digitsVal t.2.2))

/-- What `server_version_parsed` and `maria_db_server_version_parsed` do with the regex's
    captures: `btoi::<u16>` of each, **panicking** (`unwrap`) if one does not parse. -/
def versionOfCaptures : Option (Slice U8 × Slice U8 × Slice U8) → Result (Option (U16 × U16 × U16))
  | none => .ok none
  | some (a, b, c) =>
    match Trusted.btoiUnsigned .U16 a, Trusted.btoiUnsigned .U16 b, Trusted.btoiUnsigned .U16 c with
    | some x, some y, some z => .ok (some (x, y, z))
    | _, _, _ => .fail .panic

/-! ## Connect attributes -/

/-- A connect-attributes map's entries as byte lists, in the map's iteration order (opaque: the
    order is the `HashMap`'s, seeded randomly in Rust; specs never relate it across maps). -/
noncomputable def attrsEntries (m : Trusted.ConnectAttrs) : List (List U8 × List U8) :=
  (Trusted.connectAttrsEntries m).val.map (fun e => (e.1.val, e.2.val))

/-- `m` is the map the crate's reader builds from the wire entries `kvs`: a new map, then each
    entry inserted in order (`HashMap::insert`, a later key replacing an earlier one). -/
def BuiltFrom (m : Trusted.ConnectAttrs) (kvs : List (List U8 × List U8)) : Prop :=
  ∃ es : List (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit ×
      misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit),
    es.map (fun e => (cowList e.1.1, cowList e.2.1)) = kvs ∧
      m = es.foldl (fun acc e => Trusted.connectAttrsInsert acc e.1 e.2) Trusted.connectAttrsNew

/-- An optional map and optional wire entries agree: both absent, or the map is `BuiltFrom` the
    entries. -/
def AttrsMatch : Option Trusted.ConnectAttrs → Option (List (List U8 × List U8)) → Prop
  | some m, some kvs => BuiltFrom m kvs
  | none, none => True
  | _, _ => False

/-- The connection attributes on the wire: the total length (lenenc), then each key and value as
    a length-encoded string. -/
def attrsEnc (kvs : List (List U8 × List U8)) : List U8 :=
  let body := (kvs.map (fun kv => lenencStr kv.1 ++ lenencStr kv.2)).flatten
  lenencInt body.length ++ body

/-- The crate's reader of the key-value pairs filling `bs` (each by `checkedLenencStr`, with its
    quirk), with fuel; `none` if a pair is malformed. -/
def attrEntriesAux : Nat → List U8 → Option (List (List U8 × List U8))
  | 0, _ => some []
  | _ + 1, [] => some []
  | fuel + 1, bs@(_ :: _) =>
    match checkedLenencStr bs with
    | (none, _) => none
    | (some k, r) =>
      match checkedLenencStr r with
      | (none, _) => none
      | (some v, r') => (attrEntriesAux fuel r').map ((k, v) :: ·)

/-- The crate's reader of the connection attributes: the total length by `checkedLenencInt`, that
    many bytes (`none`, the length consumed, if fewer), consumed whatever they hold, and the pairs
    in them (`attrEntriesAux`; every pair takes at least 2 bytes, so the fuel suffices). -/
def connectAttrsRead (bs : List U8) : Option (List (List U8 × List U8)) × List U8 :=
  match checkedLenencInt bs with
  | (none, rest) => (none, rest)
  | (some n, rest) =>
    if rest.length < n then (none, rest)
    else (attrEntriesAux n (rest.take n), rest.drop n)

/-! ## `Protocol::HandshakeResponse41` -/

/-- How the auth response of a handshake response is framed. -/
inductive ScrambleKind where
  /-- `string<lenenc>` (`CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA`). -/
  | lenenc
  /-- a 1-byte length and the bytes (`CLIENT_SECURE_CONNECTION`). -/
  | u8
  /-- `string<NUL>` (neither). -/
  | nul
deriving DecidableEq

/-- The framing the protocol prescribes for the capability flags `caps`. -/
def scrambleKindFor (caps : Nat) : ScrambleKind :=
  if hasFlag caps CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA then .lenenc
  else if hasFlag caps CLIENT_SECURE_CONNECTION then .u8
  else .nul

/-- An auth response framed as `k`, as the crate writes it (a 1-byte-length response is cut at
    255 bytes, a `string<NUL>` one at its first `0`). -/
def scrambleEnc : ScrambleKind → List U8 → List U8
  | .lenenc, s => lenencStr s
  | .u8, s => byte (min s.length 255) :: s.take 255
  | .nul, s => nulStr s

/-- The crate's reader of an auth response, framed as `scrambleKindFor caps`. -/
def scrambleRead (caps : Nat) (bs : List U8) : Option (ScrambleKind × List U8) × List U8 :=
  let k := scrambleKindFor caps
  let r := match k with
    | .lenenc => checkedLenencStr bs
    | .u8 => checkedLenPrefixed 1 bs
    | .nul => nulStrRead bs
  (r.1.map (fun s => (k, s)), r.2)

/-- A handshake response's fields (except the connect attributes, kept as a map), as the specs
    describe them. -/
structure HsResp where
  caps : Nat
  maxPacket : Nat
  collation : Nat
  mariadbCaps : Nat
  user : List U8
  scrambleKind : ScrambleKind
  scramble : List U8
  db : Option (List U8)
  pluginName : Option (List U8)
deriving DecidableEq

/-- The framing and bytes of a `ScrambleBuf`. -/
def scrambleView : misc.raw.Either (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit)
    (misc.raw.Either (misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit)
      (misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit)) → ScrambleKind × List U8
  | .Left rb => (.lenenc, cowList rb.1)
  | .Right (.Left rb) => (.u8, cowList rb.1)
  | .Right (.Right rb) => (.nul, cowList rb.1)

/-- The `HsResp` of a `HandshakeResponse`. -/
def HsResp.of (p : packets.HandshakeResponse) : HsResp where
  caps := p.capabilities.1.val
  maxPacket := p.max_packet_size.1.val
  collation := p.collation.1.val
  mariadbCaps := p.mariadb_ext_capabilities.1.val
  user := cowList p.user.1
  scrambleKind := (scrambleView p.scramble_buf).1
  scramble := (scrambleView p.scramble_buf).2
  db := p.db_name.map (fun rb => cowList rb.1)
  pluginName := p.auth_plugin.map authPluginName

/-- A `HandshakeResponse` is the one described by `v` and the wire attributes `kvs`: its fields
    are `v`'s, its plugin is in normal form (`PluginCanonical`), its map is built from `kvs`. -/
def HsResp.Matches (p : packets.HandshakeResponse) (v : HsResp)
    (kvs : Option (List (List U8 × List U8))) : Prop :=
  HsResp.of p = v ∧ (∀ r, p.auth_plugin = some r → PluginCanonical r) ∧
    AttrsMatch p.connect_attributes kvs

/-- The crate's reader of a handshake response (`MyDeserialize for HandshakeResponse`):
    * 32 bytes (`none`, nothing consumed, if fewer), consumed whatever they hold: the capability
      flags (4, every bit kept), the max packet size (4), the collation (1), 19 filler bytes (not
      checked), MariaDB's capabilities (4, only the known bits kept);
    * the user by `nulStrRead`; the auth response by `scrambleRead`;
    * with `CLIENT_CONNECT_WITH_DB`, the database by `nulStrRead`;
    * with `CLIENT_PLUGIN_AUTH`, the plugin name: the bytes before the first `0`, consuming it, or
      **all the rest if there is no `0`** (never an error);
    * with `CLIENT_CONNECT_ATTRS`, `connectAttrsRead`.
    **Crate behaviour**: `CLIENT_PROTOCOL_41` is assumed (the old `HandshakeResponse320` is not
    read); the zstd compression level (`CLIENT_ZSTD_COMPRESSION_ALGORITHM`) and any bytes after
    the fields are left unread. -/
def hsRespRead (bs : List U8) : Option (HsResp × Option (List (List U8 × List U8))) × List U8 :=
  if bs.length < 32 then (none, bs)
  else
    let f := bs.take 32
    let field (i k : Nat) : Nat := leNat ((f.drop i).take k)
    let caps := field 0 4
    match nulStrRead (bs.drop 32) with
    | (none, r) => (none, r)
    | (some user, r1) =>
      match scrambleRead caps r1 with
      | (none, r) => (none, r)
      | (some (k, s), r2) =>
        let db : Option (Option (List U8)) × List U8 :=
          if hasFlag caps CLIENT_CONNECT_WITH_DB then
            match nulStrRead r2 with
            | (none, r) => (none, r)
            | (some d, r) => (some (some d), r)
          else (some none, r2)
        match db with
        | (none, r) => (none, r)
        | (some db, r3) =>
          let pn : Option (List U8) × List U8 :=
            if hasFlag caps CLIENT_PLUGIN_AUTH then
              (some (beforeZero r3), r3.drop ((beforeZero r3).length + 1))
            else (none, r3)
          let att : Option (Option (List (List U8 × List U8))) × List U8 :=
            if hasFlag caps CLIENT_CONNECT_ATTRS then
              match connectAttrsRead pn.2 with
              | (none, r) => (none, r)
              | (some kvs, r) => (some (some kvs), r)
            else (some none, pn.2)
          match att with
          | (none, r) => (none, r)
          | (some kvs, r5) =>
            (some ({ caps := caps, maxPacket := field 4 4, collation := field 8 1,
                     mariadbCaps := field 28 4 &&& mariadbCapabilitiesAll, user := user,
                     scrambleKind := k, scramble := s, db := db, pluginName := pn.1 }, kvs), r5)

/-- `Protocol::HandshakeResponse41` with the fields of `v` and the attributes `kvs`, as the crate
    writes it: the filler is 19 zeros and MariaDB's capabilities; the user and database are
    `nulStr`s; the auth response is framed by `v.scrambleKind` (**not** by the flags); the
    database, plugin name (its bytes and `0`, not cut at an inner `0`) and attributes are written
    when present, **whatever the capability flags say**. -/
def hsRespEnc (v : HsResp) (kvs : Option (List (List U8 × List U8))) : List U8 :=
  leBytes 4 v.caps ++ leBytes 4 v.maxPacket ++ [byte v.collation] ++ List.replicate 19 (byte 0)
    ++ leBytes 4 v.mariadbCaps ++ nulStr v.user ++ scrambleEnc v.scrambleKind v.scramble
    ++ (match v.db with | some d => nulStr d | none => [])
    ++ (match v.pluginName with | some n => n ++ [byte 0] | none => [])
    ++ (match kvs with | some kvs => attrsEnc kvs | none => [])

/-- When a handshake response written by `hsRespEnc` reads back as itself: the fields fit, the
    MariaDB capabilities have only known bits, the strings have no `0` (the auth response too
    when it is a `string<NUL>`; a 1-byte-length one has at most 255 bytes), the framing is the one
    the flags prescribe, and the database, plugin name and attributes are present iff
    `CLIENT_CONNECT_WITH_DB`, `CLIENT_PLUGIN_AUTH` and `CLIENT_CONNECT_ATTRS`. -/
def HsResp.Compatible (v : HsResp) (kvs : Option (List (List U8 × List U8))) : Prop :=
  v.caps < 2 ^ 32 ∧ v.maxPacket < 2 ^ 32 ∧ v.collation < 256 ∧
    v.mariadbCaps &&& mariadbCapabilitiesAll = v.mariadbCaps ∧ NoNul v.user ∧
    v.scrambleKind = scrambleKindFor v.caps ∧
    (v.scrambleKind = .u8 → v.scramble.length ≤ 255) ∧
    (v.scrambleKind = .nul → NoNul v.scramble) ∧
    v.db.isSome = hasFlag v.caps CLIENT_CONNECT_WITH_DB ∧ (∀ d, v.db = some d → NoNul d) ∧
    v.pluginName.isSome = hasFlag v.caps CLIENT_PLUGIN_AUTH ∧
    (∀ n, v.pluginName = some n → NoNul n) ∧
    kvs.isSome = hasFlag v.caps CLIENT_CONNECT_ATTRS

/-- `server_version ≥ (5, 5, 3)`, lexicographically: from MySQL 5.5.3 the client asks for
    `utf8mb4_general_ci` (45), before it for `utf8mb3_general_ci` (33). -/
def atLeast553 (major minor patch : Nat) : Bool :=
  major > 5 || (major == 5 && (minor > 5 || (minor == 5 && patch ≥ 3)))

/-! ## `Protocol::SSLRequest` -/

/-- An SSL request's fields. -/
structure SslReq where
  caps : Nat
  maxPacket : Nat
  charset : Nat
  mariadbCaps : Nat
deriving DecidableEq

/-- The `SslReq` of an `SslRequest`. -/
def SslReq.of (p : packets.SslRequest) : SslReq :=
  ⟨p.capabilities.1.val, p.max_packet_size.1.val, p.character_set.1.val,
   p.mariadb_capabilities.1.val⟩

/-- `Protocol::SSLRequest`: the flags (4), max packet size (4), character set (1), 19 zeros and
    MariaDB's capabilities (4). -/
def sslRequestEnc (v : SslReq) : List U8 :=
  leBytes 4 v.caps ++ leBytes 4 v.maxPacket ++ [byte v.charset] ++ List.replicate 19 (byte 0)
    ++ leBytes 4 v.mariadbCaps

/-- The crate's reader of an SSL request: 32 bytes (`none`, nothing consumed, if fewer), whatever
    the filler holds; only the known MariaDB bits are kept. Bytes after the 32 are left unread. -/
def sslRequestRead (bs : List U8) : Option SslReq × List U8 :=
  if bs.length < 32 then (none, bs)
  else
    let field (i k : Nat) : Nat := leNat ((bs.drop i).take k)
    (some ⟨field 0 4, field 4 4, field 8 1, field 28 4 &&& mariadbCapabilitiesAll⟩, bs.drop 32)

/-! ## `COM_CHANGE_USER` -/

/-- The optional tail of a `COM_CHANGE_USER` (`ComChangeUserMoreData`), except the attributes. -/
structure ChangeUserMore where
  charset : Nat
  pluginName : Option (List U8)
deriving DecidableEq

/-- The `ChangeUserMore` of a `ComChangeUserMoreData`. -/
def ChangeUserMore.of (m : packets.ComChangeUserMoreData) : ChangeUserMore :=
  ⟨m.character_set.1.val, m.auth_plugin.map authPluginName⟩

/-- A `ComChangeUserMoreData` is the one described by `v` and the wire attributes `kvs`. -/
def ChangeUserMore.Matches (m : packets.ComChangeUserMoreData) (v : ChangeUserMore)
    (kvs : Option (List (List U8 × List U8))) : Prop :=
  ChangeUserMore.of m = v ∧ (∀ r, m.auth_plugin = some r → PluginCanonical r) ∧
    AttrsMatch m.connect_attributes kvs

/-- A `COM_CHANGE_USER`'s fields (the attributes of the tail aside). -/
structure ChangeUser where
  user : List U8
  authData : List U8
  database : List U8
  moreData : Option ChangeUserMore
deriving DecidableEq

/-- The `ChangeUser` of a `ComChangeUser`. -/
def ChangeUser.of (p : packets.ComChangeUser) : ChangeUser :=
  ⟨cowList p.user.1, cowList p.auth_plugin_data.1, cowList p.database.1,
   p.more_data.map ChangeUserMore.of⟩

/-- A `ComChangeUser` is the one described by `v` and (for its tail) the wire attributes `kvs`. -/
def ChangeUser.Matches (p : packets.ComChangeUser) (v : ChangeUser)
    (kvs : Option (List (List U8 × List U8))) : Prop :=
  ChangeUser.of p = v ∧
    match p.more_data with
    | some m => (∀ r, m.auth_plugin = some r → PluginCanonical r) ∧ AttrsMatch m.connect_attributes kvs
    | none => kvs = none

/-- The crate's reader of the tail (`MyDeserialize for ComChangeUserMoreData`), given the
    capability flags `caps`: the character set (2 bytes; `none`, nothing consumed, if fewer);
    with `CLIENT_PLUGIN_AUTH` the plugin name by `nulStrRead`; with `CLIENT_CONNECT_ATTRS`
    `connectAttrsRead`. Bytes after these are left unread. -/
def changeUserMoreRead (caps : Nat) (bs : List U8) :
    Option (ChangeUserMore × Option (List (List U8 × List U8))) × List U8 :=
  if bs.length < 2 then (none, bs)
  else
    let pn : Option (Option (List U8)) × List U8 :=
      if hasFlag caps CLIENT_PLUGIN_AUTH then
        match nulStrRead (bs.drop 2) with
        | (none, r) => (none, r)
        | (some n, r) => (some (some n), r)
      else (some none, bs.drop 2)
    match pn with
    | (none, r) => (none, r)
    | (some pn, r1) =>
      let att : Option (Option (List (List U8 × List U8))) × List U8 :=
        if hasFlag caps CLIENT_CONNECT_ATTRS then
          match connectAttrsRead r1 with
          | (none, r) => (none, r)
          | (some kvs, r) => (some (some kvs), r)
        else (some none, r1)
      match att with
      | (none, r) => (none, r)
      | (some kvs, r2) => (some (⟨leNat (bs.take 2), pn⟩, kvs), r2)

/-- The crate's reader of a `COM_CHANGE_USER` (`MyDeserialize for ComChangeUser`), given the
    capability flags `caps`: the header `0x11` (`none` on an empty input; `none`, the byte
    consumed, if it differs), the user by `nulStrRead`, the auth response with a 1-byte length
    (`checkedLenPrefixed 1`) **whatever `CLIENT_SECURE_CONNECTION` says** (the crate supports only
    such servers), the database by `nulStrRead`, then, if any input is left, the tail
    (`changeUserMoreRead`). -/
def changeUserRead (caps : Nat) : List U8 →
    Option (ChangeUser × Option (List (List U8 × List U8))) × List U8
  | [] => (none, [])
  | b :: r0 =>
    if b.val ≠ 0x11 then (none, r0)
    else
      match nulStrRead r0 with
      | (none, r) => (none, r)
      | (some u, r1) =>
        match checkedLenPrefixed 1 r1 with
        | (none, r) => (none, r)
        | (some a, r2) =>
          match nulStrRead r2 with
          | (none, r) => (none, r)
          | (some d, r3) =>
            if r3 = [] then (some (⟨u, a, d, none⟩, none), [])
            else match changeUserMoreRead caps r3 with
              | (none, r) => (none, r)
              | (some (m, kvs), r4) => (some (⟨u, a, d, some m⟩, kvs), r4)

/-- The tail of a `COM_CHANGE_USER` with the fields of `v` and the attributes `kvs`, as the crate
    writes it: the character set, the plugin name (its bytes and `0`) when present, and **always**
    the attributes (an empty map when there are none: the crate acts as if
    `CLIENT_CONNECT_ATTRS` were set), whatever the capability flags. -/
def changeUserMoreEnc (v : ChangeUserMore) (kvs : List (List U8 × List U8)) : List U8 :=
  leBytes 2 v.charset ++ (match v.pluginName with | some n => n ++ [byte 0] | none => [])
    ++ attrsEnc kvs

/-- A `COM_CHANGE_USER` with the fields of `v` (and the attributes `kvs` in its tail), as the crate
    writes it: `0x11`, the user (`nulStr`), the auth response with a 1-byte length (cut at 255
    bytes), the database (`nulStr`), the tail if present. -/
def changeUserEnc (v : ChangeUser) (kvs : List (List U8 × List U8)) : List U8 :=
  byte 0x11 :: nulStr v.user ++ (byte (min v.authData.length 255) :: v.authData.take 255)
    ++ nulStr v.database ++ (match v.moreData with | some m => changeUserMoreEnc m kvs | none => [])

/-- When a tail written by `changeUserMoreEnc` reads back as itself with the flags `caps`: the
    character set fits, a plugin name (without `0`) is present iff `CLIENT_PLUGIN_AUTH`, and
    `CLIENT_CONNECT_ATTRS` is set (the attributes are always written). -/
def ChangeUserMore.Compatible (caps : Nat) (m : ChangeUserMore) : Prop :=
  m.charset < 2 ^ 16 ∧ m.pluginName.isSome = hasFlag caps CLIENT_PLUGIN_AUTH ∧
    (∀ n, m.pluginName = some n → NoNul n) ∧ hasFlag caps CLIENT_CONNECT_ATTRS = true

/-- When a `COM_CHANGE_USER` written by `changeUserEnc` reads back as itself with the flags `caps`:
    user and database without `0`, an auth response of at most 255 bytes, a compatible tail. -/
def ChangeUser.Compatible (caps : Nat) (v : ChangeUser) : Prop :=
  NoNul v.user ∧ v.authData.length ≤ 255 ∧ NoNul v.database ∧
    ∀ m, v.moreData = some m → ChangeUserMore.Compatible caps m

end Defs
