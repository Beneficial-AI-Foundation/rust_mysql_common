import Defs

/-! Statements for `struct HandshakePacket and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for HandshakePacket`: `SIZE` is `None`. -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for HandshakePacket`: on any input where it does not panic, exactly `handshakeRead` (fields, errors, and what is left of the buffer). -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : ¬ handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Handshake.of, rest.val) = handshakeRead buf.val ⦄ := by
  sorry

/-- **Bug: `MyDeserialize for HandshakePacket` panics on a server-supplied length byte in `128..135`** (with `CLIENT_SECURE_CONNECTION`): `auth_plugin_data_len as i8 - 8` overflows (`handshakePanics`). A server, or anyone in the middle before TLS, can crash a client built with overflow checks (e.g. a debug build) with the first packet. (Without overflow checks the subtraction wraps to exactly `b - 8`, the protocol's value, and the packet is read correctly.) -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (buf : io.ParseBuf) (h : handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .integerOverflow := by
  sorry

/-- `MySerialize for HandshakePacket`: appends `handshakeEnc` of the fields. -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (handshakeEnc (Handshake.of self)).length ≤ Usize.max) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ handshakeEnc (Handshake.of self) ⦄ := by
  sorry

/-- Round trip: a `Handshake.Compatible` handshake written by `handshakeEnc` reads back with the same fields (the stored length byte is the one written). With `CLIENT_PLUGIN_AUTH` the plugin name is the rest of the packet, so nothing may follow. (With `CLIENT_PLUGIN_AUTH`, a scramble of 120–127 bytes makes the reader panic instead: `Defs.handshakePanics_handshakeEnc`.) -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (hs : Handshake) (hc : hs.Compatible) (tail : List U8)
    (ht : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true → tail = []) (buf : io.ParseBuf)
    (h : buf.val = handshakeEnc hs ++ tail) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Handshake.of = some { hs with authDataLen := handshakeLenByte hs } ∧ rest.val = tail ⦄ := by
  sorry

/-- `new`: the given fields; the capabilities are split into their lower and upper 16 bits, MariaDB's capabilities are empty. The stored length byte is the scramble's length (at most 247), **without the protocol's `+ 8`**; it is not used by `serialize` (which recomputes it) or any accessor, but the derived `PartialEq`/`Debug` see it, so `new(..)` differs from `deserialize(serialize(new(..)))`. -/
theorem packets.HandshakePacket.new_spec {T1 T2 T3 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into3 : core.convert.Into T3 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
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
          pluginName := auth_plugin_name.map (fun _ => cowList c3) } ⦄ := by
  sorry

/-- `with_mariadb_ext_capabilities`: replaces MariaDB's capabilities. -/
theorem packets.HandshakePacket.with_mariadb_ext_capabilities_spec (self : packets.HandshakePacket) (flags : constants.MariadbCapabilities) :
    packets.HandshakePacket.with_mariadb_ext_capabilities self flags ⦃ p =>
      Handshake.of p = { Handshake.of self with mariadbCaps := flags.val } ⦄ := by
  sorry

/-- `into_owned`: the same fields. -/
theorem packets.HandshakePacket.into_owned_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.into_owned self ⦃ p => Handshake.of p = Handshake.of self ⦄ := by
  sorry

/-- `protocol_version`: the field. -/
theorem packets.HandshakePacket.impl.protocol_version_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.protocol_version self = ok self.protocol_version.1 := by
  sorry

/-- `server_version_ref`: the server version. -/
theorem packets.HandshakePacket.server_version_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_ref self ⦃ s => s.val = cowList self.server_version.1 ⦄ := by
  sorry

/-- `server_version_str`: the server version, lossily converted to UTF-8 (`LossyUtf8`). -/
theorem packets.HandshakePacket.server_version_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_str self ⦃ c => LossyUtf8 (cowList self.server_version.1) c ⦄ := by
  sorry

/-- `server_version_parsed`, exactly: the trusted `VERSION_RE` captures of the server version, each read by `btoi::<u16>`, **panicking** if one does not parse (`versionOfCaptures`). The regex is opaque (`Trusted.versionReCaptures`). -/
theorem packets.HandshakePacket.server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.server_version_parsed self = versionOfCaptures (Trusted.versionReCaptures s) := by
  sorry

/-- `server_version_parsed` never returns a wrong version: on ASCII input the result is the version that `^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)` captures (`versionReMatch`, by the trusted `Trusted.versionReCaptures_ascii`), and there is no panic. **Bug** (as for the date/time parsers): off ASCII, `\d` is Unicode-aware but `btoi` is not, so a server version with non-ASCII digits that the regex matches panics (`unwrap`; `server_version_parsed_eq`). -/
theorem packets.HandshakePacket.server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.server_version_parsed self ⦃ r => versionVal r = digitsTriple (versionReMatch s.val) ⦄ := by
  sorry

/-- `maria_db_server_version_parsed`, exactly: as `server_version_parsed_eq` with `MARIADB_VERSION_RE` (`Trusted.mariadbVersionReCaptures`). -/
theorem packets.HandshakePacket.maria_db_server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.maria_db_server_version_parsed self = versionOfCaptures (Trusted.mariadbVersionReCaptures s) := by
  sorry

/-- `maria_db_server_version_parsed` never returns a wrong version: as `server_version_parsed_ascii`, with `mariadbVersionReMatch` (`Trusted.mariadbVersionReCaptures_ascii`). Same **bug** off ASCII. -/
theorem packets.HandshakePacket.maria_db_server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.maria_db_server_version_parsed self ⦃ r => versionVal r = digitsTriple (mariadbVersionReMatch s.val) ⦄ := by
  sorry

/-- `connection_id`: the field. -/
theorem packets.HandshakePacket.impl.connection_id_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.connection_id self = ok self.connection_id.1 := by
  sorry

/-- `scramble_1_ref`: the 8 bytes. -/
theorem packets.HandshakePacket.scramble_1_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_1_ref self ⦃ s => s.val = self.scramble_1.val ⦄ := by
  sorry

/-- `scramble_2_ref`: the scramble, if any (at most 247 bytes: the `BareBytes<247>` maximum; documented: may include the terminating `0`). -/
theorem packets.HandshakePacket.scramble_2_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_2_ref self ⦃ o => o.map (·.val) = self.scramble_2.map (fun rb => (cowList rb.1).take 247) ⦄ := by
  sorry

/-- `nonce`: `scramble_1` then `scramble_2` without its trailing `0`, zero-padded to 20 bytes (`handshakeNonce`). -/
theorem packets.HandshakePacket.nonce_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.nonce self ⦃ v =>
      v.val = handshakeNonce self.scramble_1.val (self.scramble_2.map (fun rb => (cowList rb.1).take 247)) ⦄ := by
  sorry

/-- `capabilities`: the two halves together. -/
theorem packets.HandshakePacket.capabilities_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.capabilities self ⦃ c => c.val = self.capabilities_1.1.val ||| self.capabilities_2.1.val ⦄ := by
  sorry

/-- `mariadb_ext_capabilities`: the field. -/
theorem packets.HandshakePacket.impl.mariadb_ext_capabilities_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.mariadb_ext_capabilities self = ok self.mariadb_ext_capabilities.1 := by
  sorry

/-- `default_collation`: the field. -/
theorem packets.HandshakePacket.impl.default_collation_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.default_collation self = ok self.default_collation.1 := by
  sorry

/-- `status_flags`: the field. -/
theorem packets.HandshakePacket.impl.status_flags_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.status_flags self = ok self.status_flags.1 := by
  sorry

/-- `auth_plugin_name_ref`: the plugin name, if any. -/
theorem packets.HandshakePacket.auth_plugin_name_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_ref self ⦃ o => o.map (·.val) = self.auth_plugin_name.map (fun rb => cowList rb.1) ⦄ := by
  sorry

/-- `auth_plugin_name_str`: the plugin name, if any, lossily converted to UTF-8. -/
theorem packets.HandshakePacket.auth_plugin_name_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_str self ⦃ o =>
      optMatch (fun rb c => LossyUtf8 (cowList rb.1) c) self.auth_plugin_name o ⦄ := by
  sorry

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the plugin name without a trailing `0`. (`from_bytes` removes another trailing `0`: **a quirk**, two are removed in all.) -/
theorem packets.HandshakePacket.auth_plugin_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin self ⦃ o =>
      optMatch (fun rb r => PluginFromBytes (dropTrailingNul (cowList rb.1)) r) self.auth_plugin_name o ⦄ := by
  sorry

end mysql_common
