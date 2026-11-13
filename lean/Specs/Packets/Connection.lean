import Proofs.Packets.LocalInfilePacket
import Proofs.Packets.AuthPlugin
import Proofs.Packets.AuthMoreData
import Proofs.Packets.PublicKeyResponse
import Proofs.Packets.OldAuthSwitchRequest
import Proofs.Packets.AuthSwitchRequest
import Proofs.Packets.ParseParsecSalt
import Proofs.Packets.HandshakePacket
import Proofs.Packets.ComChangeUser
import Proofs.Packets.ComChangeUserMoreData
import Proofs.Packets.HandshakeResponse
import Proofs.Packets.SslRequest

/-!
# `src/packets/mod.rs`: the connection phase
    The connection-phase packets of `src/packets/mod.rs` (the rest of the file is in
    `Specs/Packets.lean` and the other coverage-round-4 spec files; this file should be merged into
    `Specs/Packets.lean`): `LocalInfilePacket`, `AuthPlugin` (names and wire form, not the
    scramble crypto), `AuthMoreData`, `PublicKeyResponse`, `OldAuthSwitchRequest`,
    `AuthSwitchRequest`, `parse_parsec_salt`, `HandshakePacket` (every accessor), `ComChangeUser`,
    `ComChangeUserMoreData`, `HandshakeResponse`, `SslRequest`. Headlines: exact decoding of every
    packet per its protocol layout and capability flags, **total on any input** (the handshake:
    on any input where it does not panic, with the panic case stated exactly), exact encodings,
    and round trips.

    **Patches.** 61 (plain bitflags), 62 (`AuthPlugin` / auth switch as `match`es and the private
    `plugin_uses_c_string_scramble`), 63 (handshake: `max(13, len as i8 - 8)` kept, helpers for the
    optional tail), 64 (`misc::trusted`: lossy UTF-8, the version regexes, `btoi_u16`), 67
    (`parse_parsec_salt` without iterator adapters), 70 (connect attributes through
    `misc::trusted::ConnectAttrs`, a `HashMap`; the read/write loops as recursions, so stack
    proportional to the number of attributes), 72 (renamed shadowing parameters), and the earlier
    patches the packets use (22, 23, 31, 53, 54). The statements are about the patched code.

    **Configuration.** As in `Specs/Io.lean`. The readers that go through `as usize` casts of
    wire lengths (connect attributes, length-encoded strings) take `Target64`.

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics: the handshake's
    `i8` overflow is `fail .integerOverflow`; without overflow checks it wraps to the protocol's
    value), the stack is not modelled.

    **Definitions used.** `Defs/Connection.lean` (`eofPayloadRead`, `headerRead`, `authPluginName`,
    `knownPlugin`, `IsPluginNamed`, `PluginFromBytes`, `PluginCanonical`, `isOtherPlugin`,
    `usesCStringScramble`, `authSwitchRead`, `authSwitchEnc`, `parsecSaltOk`, `Handshake`,
    `handshakeRead`, `handshakePanics`, `scramble2LenCrate`, `handshakeLenByte`, `handshakeEnc`,
    `Handshake.Compatible`, `handshakeNonce`, `versionReMatch`, `mariadbVersionReMatch`,
    `versionOfCaptures`, `capturesVal`, `versionVal`, `digitsTriple`, `LossyUtf8`,
    `optMatch`, `attrsEntries`, `BuiltFrom`, `AttrsMatch`, `attrsEnc`, `connectAttrsRead`,
    `ScrambleKind`, `scrambleKindFor`, `scrambleView`, `HsResp`, `HsResp.Matches`, `hsRespRead`,
    `hsRespEnc`, `HsResp.Compatible`, `atLeast553`, `setFlag`, `SslReq`, `sslRequestRead`,
    `sslRequestEnc`, `ChangeUser`, `ChangeUserMore`, their `Matches`/`Compatible`,
    `changeUserRead`, `changeUserMoreRead`, `changeUserEnc`, `changeUserMoreEnc`, `NoNul`,
    `nulStr`, `nulStrRead`, `dropTrailingNul`), `Defs/Packets.lean` (`statusRead`),
    `Defs/LenEnc.lean`, `Defs/Flags.lean`, `Defs/Convert.lean` (`utf8`, `IsUtf8`, `digitsVal`),
    `Defs/Bytes.lean`. Sanity lemmas about them: `Specs/DefsConn.lean`.

    **Trusted axioms** (`misc::trusted`, `FunsExternal.lean`), beyond `io::Error`'s:
    * `Trusted.versionReCaptures`, `Trusted.mariadbVersionReCaptures` (the two version regexes,
      opaque) and their properties `Trusted.versionReCaptures_ascii`,
      `Trusted.mariadbVersionReCaptures_ascii` (on ASCII input they capture exactly
      `versionReMatch` / `mariadbVersionReMatch`; checked against `regex` 1.13.1 on 621 856
      inputs, `lean/Proofs/Consistency/RegexEval/`). The `_eq` statements are exact in terms of
      the opaque captures (any input); the `_ascii` statements use the property axioms.
    * `Trusted.utf8LossyOwned` (the replaced string of `from_utf8_lossy`, opaque; only through
      `LossyUtf8`, the `*_str` accessors).
    * The connect-attributes `HashMap` (`Trusted.connectAttrsNew`, `connectAttrsInsert`,
      `connectAttrsEntries`, `connectAttrsFromStrings`, `connectAttrsIntoOwned`,
      `connectAttrsToStrings`; opaque) and `Trusted.connectAttrsEntries_new` (a new map has no
      entries; order-free). Respecting the caveat of
      `FunsExternal.lean`, no statement relates the order, bytes or equality of separately built
      maps: a serializer's bytes are stated in terms of the entries of the one map it writes
      (`attrsEntries`), and a reader's map in terms of the wire entries it inserts (`BuiltFrom`,
      never compared with the map that was written; whether its keys and values are borrowed or
      owned is left open). The bytes written for an absent map are exactly `0`
      (`connectAttrsEntries_new`).
    * `Trusted.btoiUnsigned` is an exact model (a definition), not an axiom.

    **Not covered.** `LocalInfilePacket::file_name_str` and `PublicKeyResponse::rsa_key` (not
    translated: lossy UTF-8 of an `EofBytes` field; the same conversion is stated for the
    handshake's `*_str` accessors); `AuthPlugin::init` (the scramble crypto, out of scope);
    `Debug`/`Clone`/`PartialEq`/`Hash` derives; the private helpers (`plugin_uses_c_string_scramble`,
    `handshake_auth_plugin_data_len`, `serialize_handshake_*`, `parse_*`, `*_connect_attrs*`,
    `new_scramble_buf`, `opt_connect_attrs_from_strings`; covered through their callers).

    **Behaviour to note (bugs first).**
    * **`HandshakePacket::deserialize` panics on a length byte in `128..135`** with
      `CLIENT_SECURE_CONNECTION` (`auth_plugin_data_len as i8 - 8` overflows): a server, or a
      man in the middle before TLS, can crash a client built with overflow checks (e.g. debug)
      (`deserialize_panics`); without overflow checks it wraps to exactly `b - 8` and reads
      correctly. The crate's own `serialize` writes such a byte for a 120–127-byte scramble with
      `CLIENT_PLUGIN_AUTH` (`Defs.handshakePanics_handshakeEnc`). **In every build**, for a byte
      of 136 or more it reads 13 scramble bytes instead of `b - 8` (`scramble2LenCrate`,
      `Defs.scramble2LenCrate_ne`), so it silently misreads its own packet with
      `CLIENT_PLUGIN_AUTH` and a 128–247-byte scramble (`Defs.handshakeEnc_misread`).
    * **`server_version_parsed` / `maria_db_server_version_parsed` panic** on a server version
      with non-ASCII Unicode digits that the (Unicode-aware) regex matches, since `btoi` accepts
      only ASCII digits (`unwrap`). On ASCII input they return the right version (`_ascii`).
    * The handshake reader rejects a status with bit 2 (as the OK packet does: `statusRead`), does
      not check the protocol version or the filler, keeps a plugin name's bytes after a `0` (all
      the rest of the packet is the name), and removes one trailing `0` (MySQL sometimes omits
      it); `auth_plugin` removes up to two. `new` stores the scramble length without the `+ 8`
      (unused). The serializer writes the scramble and plugin name when present, whatever the
      flags.
    * `HandshakeResponse::new` overrides `CLIENT_CONNECT_WITH_DB`, `CLIENT_PLUGIN_AUTH` and
      `CLIENT_CONNECT_ATTRS` according to its arguments. Its reader assumes `CLIENT_PROTOCOL_41`,
      reads a plugin name without `0` as the rest of the packet, and ignores the zstd level.
      Plugins are normalised (`Other` with a known name reads back as the known plugin).
    * `ComChangeUser` always frames the auth data with a 1-byte length (only
      `CLIENT_SECURE_CONNECTION` servers are supported, per the crate), reads a tail iff input is
      left, and its tail **always writes connect attributes** (empty if none), even without
      `CLIENT_CONNECT_ATTRS`; the reader then leaves them unread. It reads `character_set`
      assuming `CLIENT_PROTOCOL_41`.
    * Protocol versions: the crate follows the older protocol pages: the handshake's scramble part 2
      only with `CLIENT_SECURE_CONNECTION` (the current page: always), and a `string<NUL>` auth
      response in `HandshakeResponse41` without it (the current page has only lenenc or a 1-byte
      length; MySQL 8.0 removed `CLIENT_SECURE_CONNECTION`).
    * `OldAuthSwitchRequest` and `AuthSwitchRequest` share the header `0xFE`; `PublicKeyResponse`
      and `AuthMoreData` share `0x01`. Header-only packets leave the rest unread.
    * `AuthSwitchRequest::plugin_data` drops a trailing `0` only for the four C-string-scramble
      plugins (documented).
    * `parse_parsec_salt` requires exactly 20 bytes (the comment says "prefix").
    * Connect attributes: a repeated key keeps its last value (`HashMap::insert`); the write
      order is the map's (random) iteration order.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct LocalInfilePacket and its impls` -/

/-- `new`: the given file name (converted with `into`). -/
recall packets.LocalInfilePacket.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (file_name : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into file_name = ok c) :
    packets.LocalInfilePacket.new into file_name ⦃ p => p.file_name.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.new_spec`

/-- `file_name_ref`: the file name. -/
recall packets.LocalInfilePacket.file_name_ref_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.file_name_ref self ⦃ s => s.val = cowList self.file_name.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.file_name_ref_spec`

/-- `into_owned`: the same file name. -/
recall packets.LocalInfilePacket.into_owned_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.into_owned self ⦃ p => cowList p.file_name.1 = cowList self.file_name.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.into_owned_spec`

/-- `MyDeserialize for LocalInfilePacket`: `SIZE` is `None`. -/
recall packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for LocalInfilePacket`: total; the header `0xFB` and the file name as the rest of the packet (`eofPayloadRead 0xFB`). -/
recall packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.file_name.1), rest.val) = eofPayloadRead 0xFB buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for LocalInfilePacket`: appends `0xFB` and the file name. -/
recall packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.LocalInfilePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.file_name.1).length ≤ Usize.max) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0xFB :: cowList self.file_name.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: a `LOCAL INFILE` request (the whole packet) reads back with its file name. -/
recall packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFB :: nm) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.file_name.1) = some nm ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `enum AuthPlugin and its impls` -/

/-- `MyDeserialize for AuthPlugin`: `SIZE` is `None`. -/
recall packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for AuthPlugin`: never an error; the plugin named by the whole buffer (without one trailing `0`), which is consumed. -/
recall packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ PluginFromBytes buf.val p) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for AuthPlugin`: appends the name and `0` (a `string<NUL>`; the name is not cut at an inner `0`). -/
recall packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthPlugin) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authPluginName self).length + 1 ≤ Usize.max) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ authPluginName self ++ [byte 0] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: a serialized plugin reads back as the plugin of the same name, in normal form (`Other` holding a known name comes back as that known plugin). -/
recall packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (p : packets.AuthPlugin) (buf : io.ParseBuf) (h : buf.val = authPluginName p ++ [byte 0]) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ q, okPart r = some q ∧ IsPluginNamed (authPluginName p) q) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-- `from_bytes`: the known plugin with that name (one trailing `0` removed first), else `Other` borrowing the name. -/
recall packets.AuthPlugin.from_bytes_spec (nm : Slice U8) :
    packets.AuthPlugin.from_bytes nm ⦃ r => PluginFromBytes nm.val r ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.from_bytes_spec`

/-- `as_bytes`: the plugin's name. -/
recall packets.AuthPlugin.as_bytes_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.as_bytes self ⦃ s => s.val = authPluginName self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.as_bytes_spec`

/-- `into_owned`: the same plugin; `Other` with an owned copy of its name. -/
recall packets.AuthPlugin.into_owned_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.into_owned self ⦃ r =>
      match self with
      | .Other c => ∃ v : alloc.vec.Vec U8, r = .Other (.Owned v) ∧ v.val = cowList c
      | p => r = p ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.into_owned_spec`

/-- `borrow`: the same plugin; `Other` borrowing its name. -/
recall packets.AuthPlugin.borrow_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.borrow self ⦃ r =>
      match self with
      | .Other c => ∃ s : Slice U8, r = .Other (.Borrowed s) ∧ s.val = cowList c
      | p => r = p ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.borrow_spec`

/-- `supports_password_hash`: `mysql_native_password`, `client_ed25519` and `parsec` (documented: deterministic password hashing). -/
recall packets.AuthPlugin.supports_password_hash_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.supports_password_hash self ⦃ b =>
      b = (match self with | .MysqlNativePassword | .Ed25519 | .Parsec => true | _ => false) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthPlugin.supports_password_hash_spec`

/-! ### `struct AuthMoreData and its impls` -/

/-- `new`: the given data (converted with `into`). -/
recall packets.AuthMoreData.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (data : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into data = ok c) :
    packets.AuthMoreData.new into data ⦃ p => p.data.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.new_spec`

/-- `data`: the data. -/
recall packets.AuthMoreData.impl.data_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.impl.data self ⦃ s => s.val = cowList self.data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.impl.data_spec`

/-- `into_owned`: the same data. -/
recall packets.AuthMoreData.into_owned_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.into_owned self ⦃ p => cowList p.data.1 = cowList self.data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.into_owned_spec`

/-- `MyDeserialize for AuthMoreData`: `SIZE` is `None`. -/
recall packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for AuthMoreData`: total; the header `0x01` and the data as the rest of the packet. -/
recall packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.data.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for AuthMoreData`: appends `0x01` and the data. -/
recall packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.data.1).length ≤ Usize.max) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip (the packet is the whole buffer). -/
recall packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (data : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: data) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.data.1) = some data ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct PublicKeyResponse and its impls` -/

/-- `new`: the given key (converted with `into`). -/
recall packets.PublicKeyResponse.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (rsa_key : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into rsa_key = ok c) :
    packets.PublicKeyResponse.new into rsa_key ⦃ p => p.rsa_key.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.PublicKeyResponse.new_spec`

/-- `MyDeserialize for PublicKeyResponse`: `SIZE` is `None`. -/
recall packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for PublicKeyResponse`: total; the header `0x01` (that of `AuthMoreData`) and the key as the rest of the packet. The key is not checked to be PEM. -/
recall packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.rsa_key.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for PublicKeyResponse`: appends `0x01` and the key. -/
recall packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.PublicKeyResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.rsa_key.1).length ≤ Usize.max) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.rsa_key.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip (the packet is the whole buffer). -/
recall packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (key : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: key) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.rsa_key.1) = some key ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct OldAuthSwitchRequest and its impls` -/

/-- `new`: the packet (it has no fields besides the header). -/
recall packets.OldAuthSwitchRequest.new_eq :
    packets.OldAuthSwitchRequest.new = ok { __header := () }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.new_eq`

/-- `auth_plugin`: `mysql_old_password` (documented). -/
recall packets.OldAuthSwitchRequest.auth_plugin_eq (self : packets.OldAuthSwitchRequest) :
    packets.OldAuthSwitchRequest.auth_plugin self = ok .MysqlOldPassword

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.auth_plugin_eq`

/-- `Default`: `new()`. -/
recall packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default_eq :
    packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default = ok { __header := () }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default_eq`

/-- `MyDeserialize for OldAuthSwitchRequest`: `SIZE` is `Some(1)`. -/
recall packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 1#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for OldAuthSwitchRequest`: total; the header `0xFE` (`headerRead 0xFE`). Bytes after it are left unread, so an `AuthSwitchRequest` also parses as one: the caller must tell them apart by the packet length. -/
recall packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0xFE buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for OldAuthSwitchRequest`: appends `0xFE`. -/
recall packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.OldAuthSwitchRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0xFE] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip. -/
recall packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFE :: tail) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct AuthSwitchRequest and its impls` -/

/-- `new`: the given plugin name and data (converted with `into`). -/
recall packets.AuthSwitchRequest.new_spec {T1 T2 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (auth_plugin : T1) (plugin_data : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into auth_plugin = ok c1) (h2 : into2.into plugin_data = ok c2) :
    packets.AuthSwitchRequest.new into1 into2 auth_plugin plugin_data ⦃ p => p.auth_plugin.1 = c1 ∧ p.plugin_data.1 = c2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.new_spec`

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the name. -/
recall packets.AuthSwitchRequest.impl.auth_plugin_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.auth_plugin self ⦃ r => PluginFromBytes (cowList self.auth_plugin.1) r ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.impl.auth_plugin_spec`

/-- `plugin_data`: the data, without its last byte if that is `0` and the plugin is one whose scramble MySQL sends as a C string (`usesCStringScramble`; documented: other servers may not add the `0`). -/
recall packets.AuthSwitchRequest.impl.plugin_data_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.plugin_data self ⦃ s =>
      s.val = if usesCStringScramble (cowList self.auth_plugin.1) then dropTrailingNul (cowList self.plugin_data.1)
        else cowList self.plugin_data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.impl.plugin_data_spec`

/-- `into_owned`: the same name and data. -/
recall packets.AuthSwitchRequest.into_owned_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.into_owned self ⦃ p =>
      cowList p.auth_plugin.1 = cowList self.auth_plugin.1 ∧ cowList p.plugin_data.1 = cowList self.plugin_data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.into_owned_spec`

/-- `MyDeserialize for AuthSwitchRequest`: `SIZE` is `None`. -/
recall packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for AuthSwitchRequest`: total; `authSwitchRead` (header `0xFE`, `string<NUL>` plugin name, `string<EOF>` data). -/
recall packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)), rest.val) = authSwitchRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for AuthSwitchRequest`: appends `authSwitchEnc` of the name (cut at its first `0`) and data. -/
recall packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthSwitchRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1)).length ≤ Usize.max) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for a plugin name without `0` (the packet is the whole buffer). -/
recall packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm data : List U8) (hn : NoNul nm) (buf : io.ParseBuf) (h : buf.val = authSwitchEnc nm data) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)) = some (nm, data) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `fn parse_parsec_salt` -/

/-- `parse_parsec_salt`: total; the data itself iff it is 20 bytes, starts with `'P'` and has an iteration factor of at most 20 (`parsecSaltOk`), else `None`. (The comment calls it the "20-byte prefix", but a longer input is rejected.) -/
recall packets.parse_parsec_salt_spec (data : Slice U8) :
    packets.parse_parsec_salt data ⦃ r => r.map (·.val) = if parsecSaltOk data.val then some data.val else none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.parse_parsec_salt_spec`

/-! ### `struct HandshakePacket and its impls` -/

/-- `MyDeserialize for HandshakePacket`: `SIZE` is `None`. -/
recall packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for HandshakePacket`: on any input where it does not panic, exactly `handshakeRead` (fields, errors, and what is left of the buffer). -/
recall packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : ¬ handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Handshake.of, rest.val) = handshakeRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- **Bug: `MyDeserialize for HandshakePacket` panics on a server-supplied length byte in `128..135`** (with `CLIENT_SECURE_CONNECTION`): `auth_plugin_data_len as i8 - 8` overflows (`handshakePanics`). A server, or anyone in the middle before TLS, can crash a client built with overflow checks (e.g. a debug build) with the first packet. (Without overflow checks the subtraction wraps to exactly `b - 8`, the protocol's value, and the packet is read correctly.) -/
recall packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (buf : io.ParseBuf) (h : handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics`

/-- `MySerialize for HandshakePacket`: appends `handshakeEnc` of the fields. -/
recall packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (handshakeEnc (Handshake.of self)).length ≤ Usize.max) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ handshakeEnc (Handshake.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: a `Handshake.Compatible` handshake written by `handshakeEnc` reads back with the same fields (the stored length byte is the one written). With `CLIENT_PLUGIN_AUTH` the plugin name is the rest of the packet, so nothing may follow. (With `CLIENT_PLUGIN_AUTH`, a scramble of 120–127 bytes makes the reader panic instead: `Defs.handshakePanics_handshakeEnc`.) -/
recall packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (hs : Handshake) (hc : hs.Compatible) (tail : List U8)
    (ht : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true → tail = []) (buf : io.ParseBuf)
    (h : buf.val = handshakeEnc hs ++ tail) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Handshake.of = some { hs with authDataLen := handshakeLenByte hs } ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-- `new`: the given fields; the capabilities are split into their lower and upper 16 bits, MariaDB's capabilities are empty. The stored length byte is the scramble's length (at most 247), **without the protocol's `+ 8`**; it is not used by `serialize` (which recomputes it) or any accessor, but the derived `PartialEq`/`Debug` see it, so `new(..)` differs from `deserialize(serialize(new(..)))`. -/
recall packets.HandshakePacket.new_spec {T1 T2 T3 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into3 : core.convert.Into T3 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (protocol_version : U8) (server_version : T1) (connection_id : U32) (scramble_1 : Array U8 8#usize)
    (scramble_2 : Option T2) (capabilities : constants.CapabilityFlags) (default_collation : U8)
    (status_flags : constants.StatusFlags) (auth_plugin_name : Option T3)
    (c1 c2 c3 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h1 : into1.into server_version = ok c1)
    (h2 : ∀ x, scramble_2 = some x → into2.into x = ok c2)
    (h3 : ∀ x, auth_plugin_name = some x → into3.into x = ok c3) :
    packets.HandshakePacket.new into1 into2 into3 protocol_version server_version connection_id scramble_1 scramble_2
      capabilities default_collation status_flags auth_plugin_name ⦃ p =>
      Handshake.of p =
        { protocolVersion := protocol_version.val, serverVersion := cowList c1,
          connectionId := connection_id.val, scramble1 := scramble_1.val,
          capsLower := capabilities.val &&& 0xFFFF, collation := default_collation.val,
          status := status_flags.val, capsUpper := capabilities.val &&& 0xFFFF0000,
          authDataLen := (scramble_2.map (fun _ => min (cowList c2).length 247)).getD 0,
          mariadbCaps := 0, scramble2 := scramble_2.map (fun _ => cowList c2),
          pluginName := auth_plugin_name.map (fun _ => cowList c3) } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.new_spec`

/-- `with_mariadb_ext_capabilities`: replaces MariaDB's capabilities. -/
recall packets.HandshakePacket.with_mariadb_ext_capabilities_spec (self : packets.HandshakePacket) (flags : constants.MariadbCapabilities) :
    packets.HandshakePacket.with_mariadb_ext_capabilities self flags ⦃ p =>
      Handshake.of p = { Handshake.of self with mariadbCaps := flags.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.with_mariadb_ext_capabilities_spec`

/-- `into_owned`: the same fields. -/
recall packets.HandshakePacket.into_owned_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.into_owned self ⦃ p => Handshake.of p = Handshake.of self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.into_owned_spec`

/-- `protocol_version`: the field. -/
recall packets.HandshakePacket.impl.protocol_version_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.protocol_version self = ok self.protocol_version.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.impl.protocol_version_eq`

/-- `server_version_ref`: the server version. -/
recall packets.HandshakePacket.server_version_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_ref self ⦃ s => s.val = cowList self.server_version.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.server_version_ref_spec`

/-- `server_version_str`: the server version, lossily converted to UTF-8 (`LossyUtf8`). -/
recall packets.HandshakePacket.server_version_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_str self ⦃ c => LossyUtf8 (cowList self.server_version.1) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.server_version_str_spec`

/-- `server_version_parsed`, exactly: the trusted `VERSION_RE` captures of the server version, each read by `btoi::<u16>`, **panicking** if one does not parse (`versionOfCaptures`). The regex is opaque (`Trusted.versionReCaptures`). -/
recall packets.HandshakePacket.server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.server_version_parsed self = versionOfCaptures (Trusted.versionReCaptures s)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.server_version_parsed_eq`

/-- `server_version_parsed` never returns a wrong version: on ASCII input the result is the version that `^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)` captures (`versionReMatch`, by the trusted `Trusted.versionReCaptures_ascii`), and there is no panic. **Bug** (as for the date/time parsers): off ASCII, `\d` is Unicode-aware but `btoi` is not, so a server version with non-ASCII digits that the regex matches panics (`unwrap`; `server_version_parsed_eq`). -/
recall packets.HandshakePacket.server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.server_version_parsed self ⦃ r => versionVal r = digitsTriple (versionReMatch s.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.server_version_parsed_ascii`

/-- `maria_db_server_version_parsed`, exactly: as `server_version_parsed_eq` with `MARIADB_VERSION_RE` (`Trusted.mariadbVersionReCaptures`). -/
recall packets.HandshakePacket.maria_db_server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.maria_db_server_version_parsed self = versionOfCaptures (Trusted.mariadbVersionReCaptures s)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.maria_db_server_version_parsed_eq`

/-- `maria_db_server_version_parsed` never returns a wrong version: as `server_version_parsed_ascii`, with `mariadbVersionReMatch` (`Trusted.mariadbVersionReCaptures_ascii`). Same **bug** off ASCII. -/
recall packets.HandshakePacket.maria_db_server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.maria_db_server_version_parsed self ⦃ r => versionVal r = digitsTriple (mariadbVersionReMatch s.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.maria_db_server_version_parsed_ascii`

/-- `connection_id`: the field. -/
recall packets.HandshakePacket.impl.connection_id_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.connection_id self = ok self.connection_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.impl.connection_id_eq`

/-- `scramble_1_ref`: the 8 bytes. -/
recall packets.HandshakePacket.scramble_1_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_1_ref self ⦃ s => s.val = self.scramble_1.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.scramble_1_ref_spec`

/-- `scramble_2_ref`: the scramble, if any (at most 247 bytes: the `BareBytes<247>` maximum; documented: may include the terminating `0`). -/
recall packets.HandshakePacket.scramble_2_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_2_ref self ⦃ o => o.map (·.val) = self.scramble_2.map (fun rb => (cowList rb.1).take 247) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.scramble_2_ref_spec`

/-- `nonce`: `scramble_1` then `scramble_2` without its trailing `0`, zero-padded to 20 bytes (`handshakeNonce`). -/
recall packets.HandshakePacket.nonce_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.nonce self ⦃ v =>
      v.val = handshakeNonce self.scramble_1.val (self.scramble_2.map (fun rb => (cowList rb.1).take 247)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.nonce_spec`

/-- `capabilities`: the two halves together. -/
recall packets.HandshakePacket.capabilities_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.capabilities self ⦃ c => c.val = self.capabilities_1.1.val ||| self.capabilities_2.1.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.capabilities_spec`

/-- `mariadb_ext_capabilities`: the field. -/
recall packets.HandshakePacket.impl.mariadb_ext_capabilities_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.mariadb_ext_capabilities self = ok self.mariadb_ext_capabilities.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.impl.mariadb_ext_capabilities_eq`

/-- `default_collation`: the field. -/
recall packets.HandshakePacket.impl.default_collation_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.default_collation self = ok self.default_collation.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.impl.default_collation_eq`

/-- `status_flags`: the field. -/
recall packets.HandshakePacket.impl.status_flags_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.status_flags self = ok self.status_flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.impl.status_flags_eq`

/-- `auth_plugin_name_ref`: the plugin name, if any. -/
recall packets.HandshakePacket.auth_plugin_name_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_ref self ⦃ o => o.map (·.val) = self.auth_plugin_name.map (fun rb => cowList rb.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.auth_plugin_name_ref_spec`

/-- `auth_plugin_name_str`: the plugin name, if any, lossily converted to UTF-8. -/
recall packets.HandshakePacket.auth_plugin_name_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_str self ⦃ o =>
      optMatch (fun rb c => LossyUtf8 (cowList rb.1) c) self.auth_plugin_name o ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.auth_plugin_name_str_spec`

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the plugin name without a trailing `0`. (`from_bytes` removes another trailing `0`: **a quirk**, two are removed in all.) -/
recall packets.HandshakePacket.auth_plugin_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin self ⦃ o =>
      optMatch (fun rb r => PluginFromBytes (dropTrailingNul (cowList rb.1)) r) self.auth_plugin_name o ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakePacket.auth_plugin_spec`

/-! ### `struct ComChangeUser and its impls` -/

/-- `new`: empty user, auth data and database, no tail. -/
recall packets.ComChangeUser.new_spec :
    packets.ComChangeUser.new ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.new_spec`

/-- `with_user`: the given user (converted with `into`), or empty for `None`. -/
recall packets.ComChangeUser.with_user_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (user : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, user = some x → into.into x = ok c) :
    packets.ComChangeUser.with_user into self user ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with user := (user.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.with_user_spec`

/-- `with_database`: the given database (converted with `into`), or empty for `None`. -/
recall packets.ComChangeUser.with_database_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (database : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, database = some x → into.into x = ok c) :
    packets.ComChangeUser.with_database into self database ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with database := (database.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.with_database_spec`

/-- `with_auth_plugin_data`: the given auth data (converted with `into`), or empty for `None`. -/
recall packets.ComChangeUser.with_auth_plugin_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (auth_plugin_data : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, auth_plugin_data = some x → into.into x = ok c) :
    packets.ComChangeUser.with_auth_plugin_data into self auth_plugin_data ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with authData := (auth_plugin_data.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.with_auth_plugin_data_spec`

/-- `with_more_data`: replaces the tail. -/
recall packets.ComChangeUser.with_more_data_eq (self : packets.ComChangeUser) (more_data : Option packets.ComChangeUserMoreData) :
    packets.ComChangeUser.with_more_data self more_data = ok { self with more_data := more_data }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.with_more_data_eq`

/-- `into_owned`: the same fields; plugins stay known or `Other`, maps become `connectAttrsIntoOwned` of themselves. -/
recall packets.ComChangeUser.into_owned_spec (self : packets.ComChangeUser) :
    packets.ComChangeUser.into_owned self ⦃ p =>
      ChangeUser.of p = ChangeUser.of self ∧
        p.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin, m.connect_attributes)) =
          self.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin,
            m.connect_attributes.map Trusted.connectAttrsIntoOwned)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.into_owned_spec`

/-- `Default`: `new()`. -/
recall packets.ComChangeUser.Insts.CoreDefaultDefault.default_spec :
    packets.ComChangeUser.Insts.CoreDefaultDefault.default ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.Insts.CoreDefaultDefault.default_spec`

/-- `MyDeserialize for ComChangeUser`: `SIZE` is `None`. -/
recall packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq`

/-- `MyDeserialize for ComChangeUser`: total; `changeUserRead` with the capability flags (the fields, the tail's plugin in normal form and its map built from the wire entries; errors; what is left). -/
recall packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun p vk => ChangeUser.Matches p vk.1 vk.2) (okPart r) (changeUserRead caps.val buf.val).1 ∧
        rest.val = (changeUserRead caps.val buf.val).2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec`

/-- `MySerialize for ComChangeUser`: appends `changeUserEnc` of the fields, with the entries of the tail's map in its iteration order (none if it has no map: the crate writes an empty map, whose attributes are the single byte `0` by `Trusted.connectAttrsEntries_new`). -/
recall packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUser) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD []) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: a `ChangeUser.Compatible` request written by `changeUserEnc` reads back with the same fields, its tail's map built from the written entries. Without a tail nothing may follow (any byte would be read as a tail). -/
recall packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (v : ChangeUser) (kvs : List (List U8 × List U8))
    (hc : ChangeUser.Compatible caps.val v) (tail : List U8) (ht : v.moreData = none → tail = [])
    (buf : io.ParseBuf) (h : buf.val = changeUserEnc v kvs ++ tail) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ ChangeUser.Matches p v (v.moreData.map (fun _ => kvs))) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip`

/-! ### `struct ComChangeUserMoreData and its impls` -/

/-- `new`: the character set, no plugin, no attributes. -/
recall packets.ComChangeUserMoreData.new_spec (character_set : U16) :
    packets.ComChangeUserMoreData.new character_set ⦃ m =>
      ChangeUserMore.of m = ⟨character_set.val, none⟩ ∧ m.connect_attributes = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.new_spec`

/-- `with_auth_plugin`: replaces the plugin. -/
recall packets.ComChangeUserMoreData.with_auth_plugin_eq (self : packets.ComChangeUserMoreData) (auth_plugin : Option packets.AuthPlugin) :
    packets.ComChangeUserMoreData.with_auth_plugin self auth_plugin = ok { self with auth_plugin := auth_plugin }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.with_auth_plugin_eq`

/-- `with_connect_attributes`: replaces the attributes by the map converted from the given one (`Trusted.connectAttrsFromStrings`). -/
recall packets.ComChangeUserMoreData.with_connect_attributes_eq (self : packets.ComChangeUserMoreData) (connect_attributes : Option Trusted.StringMap) :
    packets.ComChangeUserMoreData.with_connect_attributes self connect_attributes =
      ok { self with connect_attributes := connect_attributes.map Trusted.connectAttrsFromStrings }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.with_connect_attributes_eq`

/-- `into_owned`: the same fields; the plugin stays known or `Other`, the map becomes `connectAttrsIntoOwned` of itself. -/
recall packets.ComChangeUserMoreData.into_owned_spec (self : packets.ComChangeUserMoreData) :
    packets.ComChangeUserMoreData.into_owned self ⦃ m =>
      ChangeUserMore.of m = ChangeUserMore.of self ∧
        m.auth_plugin.map isOtherPlugin = self.auth_plugin.map isOtherPlugin ∧
        m.connect_attributes = self.connect_attributes.map Trusted.connectAttrsIntoOwned ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.into_owned_spec`

/-- `MyDeserialize for ComChangeUserMoreData`: `SIZE` is `None`. -/
recall packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq`

/-- `MyDeserialize for ComChangeUserMoreData`: total; `changeUserMoreRead` with the capability flags. (The plugin name is re-parsed as an `AuthPlugin` from the borrowed bytes; the `unreachable!()` for owned bytes is indeed unreachable.) -/
recall packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun m vk => ChangeUserMore.Matches m vk.1 vk.2) (okPart r) (changeUserMoreRead caps.val buf.val).1 ∧
        rest.val = (changeUserMoreRead caps.val buf.val).2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec`

/-- `MySerialize for ComChangeUserMoreData`: appends `changeUserMoreEnc`: **the attributes are always written** (the single byte `0` if there are none, by `Trusted.connectAttrsEntries_new`), whatever the flags. -/
recall packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUserMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD []) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, with `ChangeUserMore.Compatible` flags (in particular `CLIENT_CONNECT_ATTRS`: otherwise the always-written attributes are left unread). -/
recall packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (m : ChangeUserMore) (kvs : List (List U8 × List U8))
    (hc : ChangeUserMore.Compatible caps.val m) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = changeUserMoreEnc m kvs ++ tail) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ md, okPart r = some md ∧ ChangeUserMore.Matches md m (some kvs)) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip`

/-! ### `struct HandshakeResponse and its impls` -/

/-- `new`: the auth response framed as the given flags prescribe; `CLIENT_CONNECT_WITH_DB`, `CLIENT_PLUGIN_AUTH` and `CLIENT_CONNECT_ATTRS` set or cleared by whether a database, plugin and attributes are given (overriding the caller's flags); collation `utf8mb4_general_ci` (45) for a server version from 5.5.3, else `utf8mb3_general_ci` (33); user and auth response empty for `None`; MariaDB's capabilities empty; the attributes converted (`Trusted.connectAttrsFromStrings`). -/
recall packets.HandshakeResponse.new_spec {T1 T2 T3 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into3 : core.convert.Into T3 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (scramble_buf : Option T1) (server_version : U16 × U16 × U16) (user : Option T2) (db_name : Option T3)
    (auth_plugin : Option packets.AuthPlugin) (capabilities : constants.CapabilityFlags)
    (connect_attributes : Option Trusted.StringMap) (max_packet_size : U32)
    (cs cu cd : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (hs : ∀ x, scramble_buf = some x → into1.into x = ok cs)
    (hu : ∀ x, user = some x → into2.into x = ok cu) (hd : ∀ x, db_name = some x → into3.into x = ok cd) :
    packets.HandshakeResponse.new into1 into2 into3 scramble_buf server_version user db_name auth_plugin capabilities
      connect_attributes max_packet_size ⦃ p =>
      HsResp.of p =
        { caps := setFlag (setFlag (setFlag capabilities.val CLIENT_CONNECT_WITH_DB db_name.isSome)
            CLIENT_PLUGIN_AUTH auth_plugin.isSome) CLIENT_CONNECT_ATTRS connect_attributes.isSome,
          maxPacket := max_packet_size.val,
          collation := if atLeast553 server_version.1.val server_version.2.1.val server_version.2.2.val
            then 45 else 33,
          mariadbCaps := 0, user := (user.map (fun _ => cowList cu)).getD [],
          scrambleKind := scrambleKindFor capabilities.val,
          scramble := (scramble_buf.map (fun _ => cowList cs)).getD [],
          db := db_name.map (fun _ => cowList cd), pluginName := auth_plugin.map authPluginName } ∧
        p.auth_plugin = auth_plugin ∧
        p.connect_attributes = connect_attributes.map Trusted.connectAttrsFromStrings ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.new_spec`

/-- `with_mariadb_ext_capabilities`: replaces MariaDB's capabilities. -/
recall packets.HandshakeResponse.with_mariadb_ext_capabilities_spec (self : packets.HandshakeResponse) (mariadb_ext_capabilities : constants.MariadbCapabilities) :
    packets.HandshakeResponse.with_mariadb_ext_capabilities self mariadb_ext_capabilities ⦃ p =>
      HsResp.of p = { HsResp.of self with mariadbCaps := mariadb_ext_capabilities.val } ∧
        p.auth_plugin = self.auth_plugin ∧ p.connect_attributes = self.connect_attributes ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.with_mariadb_ext_capabilities_spec`

/-- `capabilities`: the field. -/
recall packets.HandshakeResponse.impl.capabilities_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.capabilities self = ok self.capabilities.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.capabilities_eq`

/-- `mariadb_ext_capabilities`: the field. -/
recall packets.HandshakeResponse.impl.mariadb_ext_capabilities_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.mariadb_ext_capabilities self = ok self.mariadb_ext_capabilities.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.mariadb_ext_capabilities_eq`

/-- `collation`: the field. -/
recall packets.HandshakeResponse.impl.collation_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.collation self = ok self.collation.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.collation_eq`

/-- `scramble_buf`: the auth response (a 1-byte-length one at most 255 bytes, the `U8Bytes` maximum). -/
recall packets.HandshakeResponse.impl.scramble_buf_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.scramble_buf self ⦃ s =>
      s.val = if (scrambleView self.scramble_buf).1 = .u8 then (scrambleView self.scramble_buf).2.take 255
        else (scrambleView self.scramble_buf).2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.scramble_buf_spec`

/-- `user`: the user. -/
recall packets.HandshakeResponse.impl.user_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.user self ⦃ s => s.val = cowList self.user.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.user_spec`

/-- `db_name`: the database, if any. -/
recall packets.HandshakeResponse.impl.db_name_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.db_name self ⦃ o => o.map (·.val) = self.db_name.map (fun rb => cowList rb.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.db_name_spec`

/-- `auth_plugin`: the field. -/
recall packets.HandshakeResponse.impl.auth_plugin_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.auth_plugin self = ok self.auth_plugin

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.auth_plugin_eq`

/-- `connect_attributes`: the map converted to strings (`Trusted.connectAttrsToStrings`, lossy UTF-8), if any. -/
recall packets.HandshakeResponse.impl.connect_attributes_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.connect_attributes self = ok (self.connect_attributes.map Trusted.connectAttrsToStrings)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.impl.connect_attributes_eq`

/-- `MyDeserialize for HandshakeResponse`: `SIZE` is `None`. -/
recall packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for HandshakeResponse`: total; `hsRespRead` (the fields, the plugin in normal form, the map built from the wire entries; errors; what is left). -/
recall packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      optMatch (fun p vk => HsResp.Matches p vk.1 vk.2) (okPart r) (hsRespRead buf.val).1 ∧
        rest.val = (hsRespRead buf.val).2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for HandshakeResponse`: appends `hsRespEnc` of the fields, with the map's entries in its iteration order (`attrsEntries`). -/
recall packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakeResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + (hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries)).length ≤ Usize.max) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: an `HsResp.Compatible` response written by `hsRespEnc` reads back with the same fields, its plugin in normal form and its map built from the written entries. -/
recall packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (v : HsResp) (kvs : Option (List (List U8 × List U8))) (hc : v.Compatible kvs)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = hsRespEnc v kvs ++ tail) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ HsResp.Matches p v kvs) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct SslRequest and its impls` -/

/-- `new`: the given fields, MariaDB's capabilities empty. -/
recall packets.SslRequest.new_spec (capabilities : constants.CapabilityFlags) (max_packet_size : U32) (character_set : U8) :
    packets.SslRequest.new capabilities max_packet_size character_set ⦃ p =>
      SslReq.of p = ⟨capabilities.val, max_packet_size.val, character_set.val, 0⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.new_spec`

/-- `with_mariadb_capabilities`: replaces MariaDB's capabilities. -/
recall packets.SslRequest.with_mariadb_capabilities_spec (self : packets.SslRequest) (mariadb_capabilities : constants.MariadbCapabilities) :
    packets.SslRequest.with_mariadb_capabilities self mariadb_capabilities ⦃ p =>
      SslReq.of p = { SslReq.of self with mariadbCaps := mariadb_capabilities.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.with_mariadb_capabilities_spec`

/-- `capabilities`: the field. -/
recall packets.SslRequest.impl.capabilities_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.capabilities self = ok self.capabilities.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.impl.capabilities_eq`

/-- `max_packet_size`: the field. -/
recall packets.SslRequest.impl.max_packet_size_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.max_packet_size self = ok self.max_packet_size.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.impl.max_packet_size_eq`

/-- `character_set`: the field. -/
recall packets.SslRequest.impl.character_set_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.character_set self = ok self.character_set.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.impl.character_set_eq`

/-- `MyDeserialize for SslRequest`: `SIZE` is `Some(32)`. -/
recall packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = ok (some 32#usize)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for SslRequest`: total; `sslRequestRead`. -/
recall packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => ((okPart r).map SslReq.of, rest.val) = sslRequestRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for SslRequest`: appends `sslRequestEnc` of the fields. -/
recall packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SslRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 32 ≤ Usize.max) :
    packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ sslRequestEnc (SslReq.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for fields that fit and known MariaDB bits. -/
recall packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (v : SslReq) (hv : v.caps < 2 ^ 32 ∧ v.maxPacket < 2 ^ 32 ∧ v.charset < 256 ∧
      v.mariadbCaps &&& mariadbCapabilitiesAll = v.mariadbCaps)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sslRequestEnc v ++ tail) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).map SslReq.of = some v ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

end mysql_common
