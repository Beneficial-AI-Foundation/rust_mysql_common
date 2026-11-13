import Defs
import Proofs.Util.ConnHandshake

/-! Statements for `struct HandshakeResponse and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.ConnHSUtil
open core.result.Result.Insts

namespace mysql_common

/-- `new`: the auth response framed as the given flags prescribe; `CLIENT_CONNECT_WITH_DB`, `CLIENT_PLUGIN_AUTH` and `CLIENT_CONNECT_ATTRS` set or cleared by whether a database, plugin and attributes are given (overriding the caller's flags); collation `utf8mb4_general_ci` (45) for a server version from 5.5.3, else `utf8mb3_general_ci` (33); user and auth response empty for `None`; MariaDB's capabilities empty; the attributes converted (`Trusted.connectAttrsFromStrings`). -/
theorem packets.HandshakeResponse.new_spec {T1 T2 T3 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into3 : core.convert.Into T3 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
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
        p.connect_attributes = connect_attributes.map Trusted.connectAttrsFromStrings ⦄ := by
  sorry

/-- `with_mariadb_ext_capabilities`: replaces MariaDB's capabilities. -/
theorem packets.HandshakeResponse.with_mariadb_ext_capabilities_spec (self : packets.HandshakeResponse) (mariadb_ext_capabilities : constants.MariadbCapabilities) :
    packets.HandshakeResponse.with_mariadb_ext_capabilities self mariadb_ext_capabilities ⦃ p =>
      HsResp.of p = { HsResp.of self with mariadbCaps := mariadb_ext_capabilities.val } ∧
        p.auth_plugin = self.auth_plugin ∧ p.connect_attributes = self.connect_attributes ⦄ := by
  unfold packets.HandshakeResponse.with_mariadb_ext_capabilities
  step*
  simp_all [HsResp.of]

/-- `capabilities`: the field. -/
theorem packets.HandshakeResponse.impl.capabilities_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.capabilities self = ok self.capabilities.1 := by
  rfl

/-- `mariadb_ext_capabilities`: the field. -/
theorem packets.HandshakeResponse.impl.mariadb_ext_capabilities_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.mariadb_ext_capabilities self = ok self.mariadb_ext_capabilities.1 := by
  rfl

/-- `collation`: the field. -/
theorem packets.HandshakeResponse.impl.collation_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.collation self = ok self.collation.1 := by
  rfl

/-- `scramble_buf`: the auth response (a 1-byte-length one at most 255 bytes, the `U8Bytes` maximum). -/
theorem packets.HandshakeResponse.impl.scramble_buf_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.scramble_buf self ⦃ s =>
      s.val = if (scrambleView self.scramble_buf).1 = .u8 then (scrambleView self.scramble_buf).2.take 255
        else (scrambleView self.scramble_buf).2 ⦄ := by
  unfold packets.HandshakeResponse.impl.scramble_buf
  rcases hs : self.scramble_buf with rb | (rb | rb) <;> simp only [scrambleView]
  · apply WP.spec_mono (PCSUtil.lenenc_as_bytes rb)
    intro s h; simp [h]
  · obtain ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
    apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm rb)
    intro s h; simp [h, hmv]
  · apply WP.spec_mono (nullbytes_as_bytes rb)
    intro s h; simp [h]

/-- `user`: the user. -/
theorem packets.HandshakeResponse.impl.user_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.user self ⦃ s => s.val = cowList self.user.1 ⦄ := by
  unfold packets.HandshakeResponse.impl.user
  step*

/-- `db_name`: the database, if any. -/
theorem packets.HandshakeResponse.impl.db_name_spec (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.db_name self ⦃ o => o.map (·.val) = self.db_name.map (fun rb => cowList rb.1) ⦄ := by
  unfold packets.HandshakeResponse.impl.db_name
  rcases hs2 : self.db_name with _ | s2 <;> simp only
  · simp
  · step*
    simp_all

/-- `auth_plugin`: the field. -/
theorem packets.HandshakeResponse.impl.auth_plugin_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.auth_plugin self = ok self.auth_plugin := by
  unfold packets.HandshakeResponse.impl.auth_plugin
  rcases self.auth_plugin <;> rfl

/-- `connect_attributes`: the map converted to strings (`Trusted.connectAttrsToStrings`, lossy UTF-8), if any. -/
theorem packets.HandshakeResponse.impl.connect_attributes_eq (self : packets.HandshakeResponse) :
    packets.HandshakeResponse.impl.connect_attributes self = ok (self.connect_attributes.map Trusted.connectAttrsToStrings) := by
  unfold packets.HandshakeResponse.impl.connect_attributes
  rcases self.connect_attributes <;> simp [misc.trusted.connect_attrs_to_strings]

/-- `MyDeserialize for HandshakeResponse`: `SIZE` is `None`. -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for HandshakeResponse`: total; `hsRespRead` (the fields, the plugin in normal form, the map built from the wire entries; errors; what is left). -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      optMatch (fun p vk => HsResp.Matches p vk.1 vk.2) (okPart r) (hsRespRead buf.val).1 ∧
        rest.val = (hsRespRead buf.val).2 ⦄ := by
  sorry

/-- `MySerialize for HandshakeResponse`: appends `hsRespEnc` of the fields, with the map's entries in its iteration order (`attrsEntries`). -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakeResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + (hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries)).length ≤ Usize.max) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries) ⦄ := by
  sorry

/-- Round trip: an `HsResp.Compatible` response written by `hsRespEnc` reads back with the same fields, its plugin in normal form and its map built from the written entries. -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (v : HsResp) (kvs : Option (List (List U8 × List U8))) (hc : v.Compatible kvs)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = hsRespEnc v kvs ++ tail) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ HsResp.Matches p v kvs) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
