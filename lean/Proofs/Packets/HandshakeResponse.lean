import Defs
import Proofs.Util.ConnHandshake
import Proofs.Packets.AuthPlugin
import Proofs.Misc.Raw.Either

/-! Statements for `struct HandshakeResponse and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.ConnHSUtil mysql_common.Shared
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

private theorem setflag_bool (x bit : constants.CapabilityFlags) (b : Bool) :
    (if b = true then constants.CapabilityFlags.insert x bit else constants.CapabilityFlags.remove x bit)
      ⦃ r => r.val = setFlag x.val bit.val b ⦄ :=
  WP.spec_mono (setflag_spec x bit _ _) (fun r hr => by rw [hr]; cases b <;> rfl)

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
  unfold packets.HandshakeResponse.new
  obtain ⟨maj, mn, pt⟩ := server_version
  refine WP.spec_bind (Pₘ := fun c => cowList c = (scramble_buf.map (fun _ => cowList cs)).getD [])
    ?_ (fun c1 hc1 => ?_)
  · rcases scramble_buf with _ | x
    · simp [alloc.borrow.Cow.Insts.CoreDefaultDefault.default, alloc.vec.Vec.Insts.CoreDefaultDefault.default]
    · simp [hs x rfl]
  step as ⟨sb, hsb⟩
  refine WP.spec_bind (setflag_bool _ _ _) (fun k1 hk1 => ?_)
  refine WP.spec_bind (setflag_bool _ _ _) (fun k2 hk2 => ?_)
  refine WP.spec_bind (setflag_bool _ _ _) (fun k3 hk3 => ?_)
  refine WP.spec_bind (Pₘ := fun o => o = connect_attributes.map Trusted.connectAttrsFromStrings)
    ?_ (fun ca1 hca1 => ?_)
  · unfold packets.opt_connect_attrs_from_strings
    rcases connect_attributes with _ | a <;> simp [misc.trusted.connect_attrs_from_strings]
  refine WP.spec_bind (Pₘ := fun b => b = atLeast553 maj.val mn.val pt.val) ?_ (fun al hal => ?_)
  · simp only [atLeast553]
    split_ifs <;> simp_all
  refine WP.spec_bind (Pₘ := fun r => r.1.val = if al then 45 else 33) ?_ (fun ri hri => ?_)
  · split <;> step*
  refine WP.spec_bind (Pₘ := fun rb => cowList rb.1 = (user.map (fun _ => cowList cu)).getD [])
    ?_ (fun rb hrb => ?_)
  · rcases user with _ | x
    · simp [misc.raw.bytes.RawBytes.Insts.CoreDefaultDefault.default]
      exact (WP.spec_ok _).mpr rfl
    · apply WP.spec_mono (PKUtil.rawbytes_new_spec _ _ x cu (hu x rfl))
      intro r hr; simp [hr]
  refine WP.spec_bind (Pₘ := fun o => o.map (fun rb => cowList rb.1) = db_name.map (fun _ => cowList cd))
    ?_ (fun o ho => ?_)
  · rcases db_name with _ | x
    · simp
    · step with PKUtil.rawbytes_new_spec _ _ x cd (hd x rfl)
      simp_all
  simp only [constants.MariadbCapabilities.empty, bind_ok]
  step*
  have e1 : (constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB).val = CLIENT_CONNECT_WITH_DB := by
    simp [constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB, CLIENT_CONNECT_WITH_DB]
  simp_all [HsResp.of]

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
  unfold packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step*
  have hi2 : i2 = 32#usize := UScalar.eq_of_val_eq (by simp_all)
  subst hi2
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  swap
  · obtain ⟨h1a, hb1⟩ := h1
    have hs : buf.val.length < 32 := by simp [Slice.length] at hl; omega
    cases r with
    | Ok _ => simp [okPart] at h1a
    | Err e => simp [hsRespRead_eq, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, hs, hb1, optMatch, okPart]
  obtain ⟨h1a, h1b⟩ := h1
  have hl' : ¬ buf.val.length < 32 := by simp [Slice.length] at hl; omega
  cases r with
  | Err e => simp [okPart] at h1a
  | Ok pb =>
  have hpb : pb.val = buf.val.take 32 := Option.some.inj h1a
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawconst_leu32 _ pb (by simp [Slice.length, hpb]; omega) as ⟨q1, s1, k1a, k1b⟩
  cases q1 with
  | Err e => simp [okPart] at k1a
  | Ok w1 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_unchecked_leu32_spec s1 (by simp [Slice.length, k1b, hpb]; omega) as ⟨q2, s2, k2a, k2b⟩
  cases q2 with
  | Err e => simp [okPart] at k2a
  | Ok w2 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_unchecked_u8_spec s2 (by simp [Slice.length, k2b, k1b, hpb]; omega) as ⟨q3, s3, k3a, k3b⟩
  cases q3 with
  | Err e => simp [okPart] at k3a
  | Ok w3 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_skip 19#usize s3 (by simp [Slice.length, k3b, k2b, k1b, hpb]; omega) as ⟨q4, s4, k4a, k4b⟩
  cases q4 with
  | Err e => simp [okPart] at k4a
  | Ok w4 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawconst_leu32 _ s4 (by simp [Slice.length, k4b, k3b, k2b, k1b, hpb]; omega) as ⟨q5, s5, k5a, k5b⟩
  cases q5 with
  | Err e => simp [okPart] at k5a
  | Ok w5 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  obtain ⟨i3, ph3⟩ := w1
  obtain ⟨i4, ph4⟩ := w5
  have e1 : s1.val = (buf.val.take 32).drop 4 := by rw [k1b, hpb]
  have e2 : s2.val = (buf.val.take 32).drop 8 := by rw [k2b, e1, List.drop_drop]
  have e3 : s3.val = (buf.val.take 32).drop 9 := by rw [k3b, e2, List.drop_drop]
  have e4 : s4.val = (buf.val.take 32).drop 28 := by rw [k4b, e3, List.drop_drop]
  have vc : i3.val = leNat (List.take 4 (List.drop 0 (List.take 32 buf.val))) := by
    rw [List.drop_zero, ← hpb]; exact Option.some.inj k1a
  have vmp : w2.1.val = leNat (List.take 4 (List.drop 4 (List.take 32 buf.val))) := by
    rw [← e1]; exact Option.some.inj k2a
  have vco : w3.1.val = leNat (List.take 1 (List.drop 8 (List.take 32 buf.val))) := by
    rw [← e2]; exact Option.some.inj k3a
  have vmc : i4.val = leNat (List.take 4 (List.drop 28 (List.take 32 buf.val))) := by
    rw [← e4]; exact Option.some.inj k5a
  have hvc : leNat (List.take 4 (List.take 32 buf.val)) = i3.val := by rw [vc, List.drop_zero]
  step with CAUtil.parse_null_bytes_spec as ⟨r6, buf2, h6⟩
  rw [h1b] at h6
  rcases hn : nulStrRead (buf.val.drop 32) with ⟨_ | user, r1v⟩ <;> rw [hn] at h6 <;> simp only [Prod.mk.injEq] at h6
  · obtain ⟨h6a, h6b⟩ := h6
    cases r6 with
    | Ok _ => simp [okPart] at h6a
    | Err e => simp [hsRespRead_eq, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, optMatch, h6b, hl', hn]
  obtain ⟨h6a, h6b⟩ := h6
  cases r6 with
  | Err e => simp [okPart] at h6a
  | Ok rbu =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with scramble_step h64 as ⟨r7, buf3, h7⟩
  rw [h6b] at h7
  rcases hsc : scrambleRead i3.val r1v with ⟨_ | ⟨k, sc⟩, r2v⟩ <;> rw [hsc] at h7 <;> simp only [Prod.mk.injEq] at h7
  · obtain ⟨h7a, h7b⟩ := h7
    cases r7 with
    | Ok _ => simp [okPart] at h7a
    | Err e =>
      simp [hsRespRead_eq, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, optMatch, h7b, hl', hn, hsc, hvc]
  obtain ⟨h7a, h7b⟩ := h7
  cases r7 with
  | Err e => simp [okPart] at h7a
  | Ok sb =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with db_step as ⟨r8, buf4, h8⟩
  rw [h7b] at h8
  rcases hdbr : dbRead i3.val r2v with ⟨_ | dbo, r3v⟩ <;> rw [hdbr] at h8 <;> simp only [Prod.mk.injEq] at h8
  · obtain ⟨h8a, h8b⟩ := h8
    cases r8 with
    | Ok _ => simp [okPart] at h8a
    | Err e =>
      simp [hsRespRead_eq, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, optMatch, h8b, hl', hn, hsc, hvc, hdbr]
  obtain ⟨h8a, h8b⟩ := h8
  cases r8 with
  | Err e => simp [okPart] at h8a
  | Ok dbv =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with hr_plugin_step as ⟨ap, buf5, h9a, h9b⟩
  rw [h8b] at h9a
  simp only [constants.CapabilityFlags.from_bits_retain_eq]
  step with CAUtil.opt_connect_attrs_step h64 as ⟨r9, buf6, h10a, h10b⟩
  have hus : cowList rbu.1 = user := Option.some.inj h6a
  have hsbv : scrambleView sb = (k, sc) := Option.some.inj h7a
  have hdbv : dbv.map (fun rb => cowList rb.1) = dbo := Option.some.inj h8a
  have hcl : i3.val &&& capabilityFlagsAll = i3.val := and_all32 _ i3.hBounds
  rcases hat : CAUtil.attRead i3.val buf5.val with ⟨_ | kvo, r5v⟩ <;> rw [hat] at h10a h10b <;> simp only at h10a h10b
  · cases r9 with
    | Ok _ => simp [okPart] at h10b
    | Err e =>
      have hb5 : buf5.val = (hrPnRead i3.val r3v).2 := by rw [← h9a]
      rw [hb5] at hat
      simp [hsRespRead_eq, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, optMatch,
        h10a, hl', hn, hsc, hvc, hdbr, hat]
  · obtain ⟨o, ho, hom⟩ := h10b
    cases r9 with
    | Err e => simp [okPart] at ho
    | Ok o' =>
    simp only [okPart, Option.some.injEq] at ho
    subst ho
    step as ⟨cfx, hcfx⟩
    subst hcfx
    step with constants.CapabilityFlags.from_bits_truncate_spec as ⟨f1, hf1⟩
    step as ⟨c1, hc1⟩
    step with mariadb_from_bits_truncate_spec as ⟨f2, hf2⟩
    step as ⟨c2, hc2⟩
    have hb5 : buf5.val = (hrPnRead i3.val r3v).2 := by rw [← h9a]
    have hpn1 : ap.map authPluginName = (hrPnRead i3.val r3v).1 := by rw [← h9a]
    rw [hb5] at hat
    rw [hsRespRead_eq]
    simp only [hl', ↓reduceIte, hn, List.drop_zero, hvc, hsc, hdbr, hat]
    refine ⟨?_, h10a⟩
    simp only [okPart, optMatch, HsResp.Matches]
    refine ⟨?_, h9b, hom⟩
    simp [HsResp.of, hc1, hc2, hf1, hf2, hcl, hus, hsbv, hdbv, hpn1, vmp, vco, vmc]

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
  have hlen := PKUtil.slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.HandshakeResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
  rintro ⟨r, rest⟩ ⟨hm, hr⟩
  rw [h, hsRespRead_enc v kvs hc tail hlen] at hm hr
  refine ⟨?_, hr⟩
  cases hp : okPart r with
  | none => rw [hp] at hm; simp [optMatch] at hm
  | some p => rw [hp] at hm; exact ⟨p, rfl, hm⟩

end mysql_common
