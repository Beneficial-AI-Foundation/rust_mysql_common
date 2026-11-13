import Defs
import Proofs.Util.ConnAuth
import Proofs.Packets.AuthPlugin

/-! Statements for `struct AuthSwitchRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

private theorem uses_c_string_aux (nm : Slice U8) :
    packets.plugin_uses_c_string_scramble nm ⦃ b => b = usesCStringScramble nm.val ⦄ := by
  unfold packets.plugin_uses_c_string_scramble
  apply WP.spec_bind (Pₘ := fun s : Slice U8 => s.val = dropTrailingNul nm.val)
  · exact drop_nul_spec nm
  · intro name1 hn1
    have key : ∀ (p : packets.AuthPlugin) (n : String), knownPlugin (utf8 n) = some p → name1.val = utf8 n →
        usesCStringScramble nm.val = (match p with
          | .MysqlNativePassword | .CachingSha2Password | .Sha256Password | .MysqlOldPassword => true
          | _ => false) := by
      intro p n hk he
      simp only [usesCStringScramble, ← hn1, he, hk]
      cases p <;> rfl
    step with slice_u8_eq_spec as ⟨b0, hb0⟩
    split
    · simp [key _ _ knownPlugin_MysqlNativePassword (by simpa using hb0.mp ‹_›)]
    · have n0 : name1.val ≠ utf8 "mysql_native_password" := by
        intro h; exact ‹¬b0 = true› (hb0.mpr (by simpa using h))
      step with slice_u8_eq_spec as ⟨b1, hb1⟩
      split
      · simp [key _ _ knownPlugin_CachingSha2Password (by simpa using hb1.mp ‹_›)]
      · have n1 : name1.val ≠ utf8 "caching_sha2_password" := by
          intro h; exact ‹¬b1 = true› (hb1.mpr (by simpa using h))
        step with slice_u8_eq_spec as ⟨b2, hb2⟩
        split
        · simp [key _ _ knownPlugin_Sha256Password (by simpa using hb2.mp ‹_›)]
        · have n2 : name1.val ≠ utf8 "sha256_password" := by
            intro h; exact ‹¬b2 = true› (hb2.mpr (by simpa using h))
          apply WP.spec_mono (slice_u8_eq_spec name1 packets.MYSQL_OLD_PASSWORD_PLUGIN_NAME)
          intro b3 hb3
          by_cases h3 : name1.val = utf8 "mysql_old_password"
          · rw [key _ _ knownPlugin_MysqlOldPassword h3]; simpa [h3] using hb3
          · have : b3 = false := by
              cases b3
              · rfl
              · exact absurd (by simpa using hb3) h3
            rw [this]
            simp only [usesCStringScramble, ← hn1]
            cases hk : knownPlugin name1.val with
            | none => rfl
            | some p =>
              have hn := knownPlugin_name hk
              cases p <;> simp_all [authPluginName]

/-- `new`: the given plugin name and data (converted with `into`). -/
theorem packets.AuthSwitchRequest.new_spec {T1 T2 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (auth_plugin : T1) (plugin_data : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into auth_plugin = ok c1) (h2 : into2.into plugin_data = ok c2) :
    packets.AuthSwitchRequest.new into1 into2 auth_plugin plugin_data ⦃ p => p.auth_plugin.1 = c1 ∧ p.plugin_data.1 = c2 ⦄ := by
  unfold packets.AuthSwitchRequest.new misc.raw.int.ConstU8.new
  step*

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the name. -/
theorem packets.AuthSwitchRequest.impl.auth_plugin_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.auth_plugin self ⦃ r => PluginFromBytes (cowList self.auth_plugin.1) r ⦄ := by
  unfold packets.AuthSwitchRequest.impl.auth_plugin
  step with null_as_bytes_spec as ⟨s, hs⟩
  apply WP.spec_mono (packets.AuthPlugin.from_bytes_spec s)
  intro r hr; rwa [hs] at hr

/-- `plugin_data`: the data, without its last byte if that is `0` and the plugin is one whose scramble MySQL sends as a C string (`usesCStringScramble`; documented: other servers may not add the `0`). -/
theorem packets.AuthSwitchRequest.impl.plugin_data_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.plugin_data self ⦃ s =>
      s.val = if usesCStringScramble (cowList self.auth_plugin.1) then dropTrailingNul (cowList self.plugin_data.1)
        else cowList self.plugin_data.1 ⦄ := by
  unfold packets.AuthSwitchRequest.impl.plugin_data
  step with eof_as_bytes_spec as ⟨data, hd⟩
  step with null_as_bytes_spec as ⟨s, hs⟩
  step with uses_c_string_aux as ⟨b, hb⟩
  rw [hs] at hb
  split
  · rename_i hbt
    rw [hbt] at hb
    apply WP.spec_mono (drop_nul_spec data)
    intro r hr; rw [hr, hd, ← hb]; simp
  · rename_i hbf
    have : usesCStringScramble (cowList self.auth_plugin.1) = false := by
      cases hh : usesCStringScramble (cowList self.auth_plugin.1)
      · rfl
      · exact absurd (hb.trans hh) hbf
    simp [this, hd]

/-- `into_owned`: the same name and data. -/
theorem packets.AuthSwitchRequest.into_owned_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.into_owned self ⦃ p =>
      cowList p.auth_plugin.1 = cowList self.auth_plugin.1 ∧ cowList p.plugin_data.1 = cowList self.plugin_data.1 ⦄ := by
  unfold packets.AuthSwitchRequest.into_owned
  step*

/-- `MyDeserialize for AuthSwitchRequest`: `SIZE` is `None`. -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for AuthSwitchRequest`: total; `authSwitchRead` (header `0xFE`, `string<NUL>` plugin name, `string<EOF>` data). -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)), rest.val) = authSwitchRead buf.val ⦄ := by
  unfold packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 254#u8 packets.InvalidAuthSwitchRequestHeader.Insts.CoreErrorError
    packets.InvalidAuthSwitchRequestHeader.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    rw [hb] at h1
    obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e => simp [authSwitchRead, hb]
  | cons b t =>
    rw [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Err e =>
      have : b.val ≠ 254 := by simpa using hr
      simp [authSwitchRead, this, hb1]
    | Ok v =>
      have : b.val = 254 := by simpa using hr
      simp only [branch_ok]
      step with parse_null_bytes_spec as ⟨r2, buf2, h2⟩
      rw [hb1] at h2
      cases r2 with
      | Err e =>
        simp only [okPart_Err, Option.map_none] at h2
        simp only [authSwitchRead, this, ne_eq, not_true_eq_false, ite_false, ← h2]
        simp
      | Ok rb =>
        simp only [okPart_Ok, Option.map_some] at h2
        simp only [branch_ok]
        step with parse_eof_bytes_spec as ⟨r3, buf3, h3a, h3b⟩
        cases r3 with
        | Err e => simp at h3a
        | Ok rb1 =>
          simp at h3a
          simp [authSwitchRead, this, ← h2, h3a, h3b]

/-- `MySerialize for AuthSwitchRequest`: appends `authSwitchEnc` of the name (cut at its first `0`) and data. -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthSwitchRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1)).length ≤ Usize.max) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1) ⦄ := by
  unfold packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize
  have hl : buf.length + (authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1)).length =
      buf.length + 1 + (beforeZero (cowList self.auth_plugin.1)).length + 1 + (cowList self.plugin_data.1).length := by
    simp [authSwitchEnc, nulStr]; omega
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  apply WP.spec_bind (Pₘ := fun buf2 : alloc.vec.Vec U8 => buf2.val = buf1.val ++ beforeZero (cowList self.auth_plugin.1) ++ [byte 0])
  · apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro s hs
    apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf1 ?_)
    · intro b hb; rw [hb, hs]
    · have e1 : buf1.length = buf.length + 1 := by simp [alloc.vec.Vec.length, h1]
      rw [e1, hs]; omega
  · intro buf2 h2
    apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro s hs
    apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf2 ?_)
    · intro b hb; simp [hb, h2, h1, hs, authSwitchEnc, nulStr, byte]; rfl
    · have e2 : buf2.length = buf.length + 1 + (beforeZero (cowList self.auth_plugin.1)).length + 1 := by
        simp [alloc.vec.Vec.length, h2, h1]; omega
      have e3 : s.length = (cowList self.plugin_data.1).length := by simp [Slice.length, hs]
      rw [e2, e3]; omega

/-- Round trip, for a plugin name without `0` (the packet is the whole buffer). -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm data : List U8) (hn : NoNul nm) (buf : io.ParseBuf) (h : buf.val = authSwitchEnc nm data) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)) = some (nm, data) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  have e : authSwitchRead buf.val = (some (nm, data), []) := by
    rw [h]
    simp only [authSwitchEnc, authSwitchRead]
    simp [nulStrRead_nulStr nm data hn, byte_val]
  rw [e] at hr
  simpa using hr

end mysql_common
