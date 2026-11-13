import Defs
import Proofs.Util.ConnHandshake
import Proofs.Packets.AuthPlugin
import Proofs.Misc.Raw.Either

/-! Statements for `struct HandshakeResponse and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.ConnHSUtil
open core.result.Result.Insts

namespace mysql_common

attribute [local step] packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec CAUtil.serialize_connect_attrs_spec

private theorem new_scramble_buf_spec (caps : constants.CapabilityFlags)
    (sb : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    packets.new_scramble_buf caps sb ⦃ e => scrambleView e = (scrambleKindFor caps.val, cowList sb) ⦄ := by
  unfold packets.new_scramble_buf
  step with PKUtil.caps_contains_spec as ⟨b, hb⟩
  have h1 : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA).val = CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA, CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA]
  have h2 : (constants.CapabilityFlags.CLIENT_SECURE_CONNECTION).val = CLIENT_SECURE_CONNECTION := by
    simp [constants.CapabilityFlags.CLIENT_SECURE_CONNECTION, CLIENT_SECURE_CONNECTION]
  rw [h1] at hb
  split
  · step*
    simp_all [scrambleView, scrambleKindFor]
  · step with PKUtil.caps_contains_spec as ⟨b1, hb1⟩
    rw [h2] at hb1
    split
    · step*
      simp_all [scrambleView, scrambleKindFor]
    · step*
      simp_all [scrambleView, scrambleKindFor]

attribute [local step] new_scramble_buf_spec

set_option maxHeartbeats 8000000 in
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
  unfold packets.HandshakeResponse.new packets.opt_connect_attrs_from_strings
  obtain ⟨maj, mn, pt⟩ := server_version
  have hs2 : ∀ x, scramble_buf = some x → into1.into x ⦃ c => c = cs ⦄ := by
    intro x hx; rw [hs x hx]; simp
  have e1 : (constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB).val = CLIENT_CONNECT_WITH_DB := by
    simp [constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB, CLIENT_CONNECT_WITH_DB]
  have e2 : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH).val = CLIENT_PLUGIN_AUTH := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH, CLIENT_PLUGIN_AUTH]
  have e3 : (constants.CapabilityFlags.CLIENT_CONNECT_ATTRS).val = CLIENT_CONNECT_ATTRS := by
    simp [constants.CapabilityFlags.CLIENT_CONNECT_ATTRS, CLIENT_CONNECT_ATTRS]
  rcases scramble_buf with _ | x1 <;> rcases user with _ | x2 <;> rcases db_name with _ | x3 <;>
    rcases auth_plugin with _ | ap <;> rcases connect_attributes with _ | ca <;>
    simp only [alloc.borrow.Cow.Insts.CoreDefaultDefault.default, alloc.vec.Vec.Insts.CoreDefaultDefault.default, bind_tc_ok, core.option.Option.is_some, Option.isSome_some,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, misc.trusted.connect_attrs_from_strings]
  all_goals
    try have hs' := hs2 _ rfl
    try have hu0 := hu _ rfl
    try have hd0 := hd _ rfl
    repeat' (first | step | split | (simp only [↓reduceIte, constants.MariadbCapabilities.empty, bind_ok]))
  all_goals simp_all [HsResp.of, setFlag, atLeast553]
  all_goals omega
  all_goals sorry

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

private theorem scramble_ser (sb : misc.raw.Either (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit)
      (misc.raw.Either (misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit)
        (misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit))) (buf : alloc.vec.Vec U8)
    (h : buf.length + (scrambleEnc (scrambleView sb).1 (scrambleView sb).2).length ≤ Usize.max) :
    misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize
      (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize
        misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple)
      (misc.raw.Either.Insts.Mysql_commonProtoMySerialize
        (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize
          misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple)
        (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize
          misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple)) sb buf
      ⦃ b => b.val = buf.val ++ scrambleEnc (scrambleView sb).1 (scrambleView sb).2 ⦄ := by
  rcases sb with rb | (rb | rb) <;>
    simp only [misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_left,
      misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_right, scrambleView, scrambleEnc] at h ⊢
  · exact PKUtil.lenenc_ser rb buf h
  · apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro sl hsl
    apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec sl buf
      (by simp only [Slice.length, hsl]; simp [alloc.vec.Vec.length] at h ⊢; omega))
    intro b hb; rw [hb, hsl]; simp [Slice.length, hsl]
  · exact nullbytes_raw_ser rb buf h

private theorem tail_ser (db : Option (misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit))
    (ap : Option packets.AuthPlugin) (ca : Option Trusted.ConnectAttrs) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((db.map (fun rb => nulStr (cowList rb.1))).getD [] ++
      (ap.map (fun p => authPluginName p ++ [byte 0])).getD [] ++
      (ca.map (fun m => attrsEnc (attrsEntries m))).getD []).length ≤ Usize.max) :
    packets.serialize_handshake_response_tail db ap ca buf ⦃ b => b.val = buf.val ++
      ((db.map (fun rb => nulStr (cowList rb.1))).getD [] ++
      (ap.map (fun p => authPluginName p ++ [byte 0])).getD [] ++
      (ca.map (fun m => attrsEnc (attrsEntries m))).getD []) ⦄ := by
  unfold packets.serialize_handshake_response_tail packets.serialize_handshake_response_auth_plugin
    packets.serialize_handshake_response_connect_attrs
  rcases db with _ | rb <;> rcases ap with _ | p <;> rcases ca with _ | m <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, List.append_nil,
      List.nil_append, List.length_append] at h ⊢
  all_goals step*
  all_goals (simp_all [alloc.vec.Vec.length]; try omega)

/-- `MySerialize for HandshakeResponse`: appends `hsRespEnc` of the fields, with the map's entries in its iteration order (`attrsEntries`). -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakeResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + (hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries)).length ≤ Usize.max) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries) ⦄ := by
  unfold packets.HandshakeResponse.Insts.Mysql_commonProtoMySerialize.serialize
  have hl : buf.val.length + (hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries)).length ≤ Usize.max := h
  have ht : (hsRespEnc (HsResp.of self) (self.connect_attributes.map attrsEntries)) =
      leBytes 4 self.capabilities.1.val ++ leBytes 4 self.max_packet_size.1.val ++ [byte self.collation.1.val] ++
        List.replicate 19 (byte 0) ++ leBytes 4 self.mariadb_ext_capabilities.1.val ++ nulStr (cowList self.user.1) ++
        scrambleEnc (scrambleView self.scramble_buf).1 (scrambleView self.scramble_buf).2 ++
        ((self.db_name.map (fun rb => nulStr (cowList rb.1))).getD [] ++
          (self.auth_plugin.map (fun p => authPluginName p ++ [byte 0])).getD [] ++
          (self.connect_attributes.map (fun m => attrsEnc (attrsEntries m))).getD []) := by
    unfold hsRespEnc HsResp.of
    rcases self.db_name <;> rcases self.auth_plugin <;> rcases self.connect_attributes <;> simp
  rw [ht] at hl ⊢
  simp only [List.length_append, List.length_cons, PBUtil.length_leBytes, List.length_replicate,
    List.length_nil] at hl
  step with const_caps_u32_ser self.capabilities buf (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b1, h1⟩
  step with PCSUtil.rawint_u32_serialize self.max_packet_size b1 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b2, h2⟩
  step with PCSUtil.rawint_u8_serialize self.collation b2 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b3, h3⟩
  step as ⟨sl, hsl⟩
  have hsl' : sl.val = List.replicate 19 (byte 0) := by rw [hsl]; simp [Array.repeat]; rfl
  clear hsl
  step with IntAndMisc.put_slice_spec b3 sl (by simp only [alloc.vec.Vec.length, Slice.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b4, h4⟩
  step with const_mariadb_u32_ser self.mariadb_ext_capabilities b4 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b5, h5⟩
  step with nullbytes_raw_ser self.user b5 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b6, h6⟩
  step with scramble_ser self.scramble_buf b6 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega) as ⟨b7, h7⟩
  apply WP.spec_mono (tail_ser self.db_name self.auth_plugin self.connect_attributes b7 (by simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega))
  intro b hb
  rw [hb, h7, h6, h5, h4, h3, h2, h1, hsl']
  simp [PCSUtil.byte_eq_self]

/-- Round trip: an `HsResp.Compatible` response written by `hsRespEnc` reads back with the same fields, its plugin in normal form and its map built from the written entries. -/
theorem packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (v : HsResp) (kvs : Option (List (List U8 × List U8))) (hc : v.Compatible kvs)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = hsRespEnc v kvs ++ tail) :
    packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ HsResp.Matches p v kvs) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
