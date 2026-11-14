import Defs
import Proofs.Util.ConnAuth
import Proofs.Packets.AuthPlugin
import Proofs.Defs.LemmasConn

/-! Statements for `struct ComChangeUserMoreData and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil
open core.result.Result.Insts

namespace mysql_common

/-- `new`: the character set, no plugin, no attributes. -/
theorem packets.ComChangeUserMoreData.new_spec (character_set : U16) :
    packets.ComChangeUserMoreData.new character_set ⦃ m =>
      ChangeUserMore.of m = ⟨character_set.val, none⟩ ∧ m.connect_attributes = none ⦄ := by
  unfold packets.ComChangeUserMoreData.new
  step*
  simp [ChangeUserMore.of, *]

/-- `with_auth_plugin`: replaces the plugin. -/
theorem packets.ComChangeUserMoreData.with_auth_plugin_eq (self : packets.ComChangeUserMoreData) (auth_plugin : Option packets.AuthPlugin) :
    packets.ComChangeUserMoreData.with_auth_plugin self auth_plugin = ok { self with auth_plugin := auth_plugin } := by
  rfl

/-- `with_connect_attributes`: replaces the attributes by the map converted from the given one (`Trusted.connectAttrsFromStrings`). -/
theorem packets.ComChangeUserMoreData.with_connect_attributes_eq (self : packets.ComChangeUserMoreData) (connect_attributes : Option Trusted.StringMap) :
    packets.ComChangeUserMoreData.with_connect_attributes self connect_attributes =
      ok { self with connect_attributes := connect_attributes.map Trusted.connectAttrsFromStrings } := by
  unfold packets.ComChangeUserMoreData.with_connect_attributes
  cases connect_attributes <;> simp [misc.trusted.connect_attrs_from_strings]

/-- `into_owned`: the same fields; the plugin stays known or `Other`, the map becomes `connectAttrsIntoOwned` of itself. -/
theorem packets.ComChangeUserMoreData.into_owned_spec (self : packets.ComChangeUserMoreData) :
    packets.ComChangeUserMoreData.into_owned self ⦃ m =>
      ChangeUserMore.of m = ChangeUserMore.of self ∧
        m.auth_plugin.map isOtherPlugin = self.auth_plugin.map isOtherPlugin ∧
        m.connect_attributes = self.connect_attributes.map Trusted.connectAttrsIntoOwned ⦄ := by
  obtain ⟨cs, ap, ca⟩ := self
  unfold packets.ComChangeUserMoreData.into_owned
  cases ap with
  | none =>
    cases ca <;> simp [ChangeUserMore.of, misc.trusted.connect_attrs_into_owned]
  | some x =>
    step with packets.AuthPlugin.into_owned_spec as ⟨y, hy⟩
    have hn : authPluginName y = authPluginName x ∧ isOtherPlugin y = isOtherPlugin x := by
      cases x <;> simp_all [authPluginName, isOtherPlugin]
      all_goals (obtain ⟨v, rfl, hv⟩ := hy; simp [hv])
    cases ca <;> simp [ChangeUserMore.of, misc.trusted.connect_attrs_into_owned, hn]

/-- `MyDeserialize for ComChangeUserMoreData`: `SIZE` is `None`. -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  simp [packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE]

/-- `MyDeserialize for ComChangeUserMoreData`: total; `changeUserMoreRead` with the capability flags. (The plugin name is re-parsed as an `AuthPlugin` from the borrowed bytes; the `unreachable!()` for owned bytes is indeed unreachable.) -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun m vk => ChangeUserMore.Matches m vk.1 vk.2) (okPart r) (changeUserMoreRead caps.val buf.val).1 ∧
        rest.val = (changeUserMoreRead caps.val buf.val).2 ⦄ := by
  unfold packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize
  rw [changeUserMoreRead_eq]
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec as ⟨r1, b1, h1⟩
  by_cases hl : 2 ≤ buf.length
  · rw [ite_eq_left hl] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have hnl : ¬ (↑buf : List U8).length < 2 := by simp [Slice.length] at hl; omega
    simp only [hnl, ite_false]
    cases r1 with
    | Err e => simp at h1a
    | Ok val =>
      simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h1a
      simp only [CoreOpsTry.branch, bind_ok]
      step with plugin_step as ⟨r2, b2, h2a, h2b⟩
      rw [h1b] at h2a h2b
      cases hp : pnRead caps.val ((↑buf : List U8).drop 2) with
      | mk o1 rr1 =>
        rw [hp] at h2a h2b
        simp only at h2a h2b ⊢
        cases o1 with
        | none =>
          cases r2 with
          | Ok _ => simp at h2b
          | Err e =>
            simp only [bind_ok, from_residual_eq]
            exact (WP.spec_ok _).mpr ⟨by simp [optMatch], h2a⟩
        | some pn =>
          obtain ⟨o, ho, hon, hoc⟩ := h2b
          cases r2 with
          | Err e => simp at ho
          | Ok o' =>
            simp only [okPart_Ok, Option.some.injEq] at ho
            subst ho
            simp only [bind_ok]
            step with opt_connect_attrs_step h64 as ⟨r3, b3, h3a, h3b⟩
            rw [h2a] at h3a h3b
            cases ha : attRead caps.val rr1 with
            | mk o2 rr2 =>
              rw [ha] at h3a h3b
              simp only at h3a h3b ⊢
              cases o2 with
              | none =>
                cases r3 with
                | Ok _ => simp at h3b
                | Err e =>
                  simp only [bind_ok, from_residual_eq]
                  exact (WP.spec_ok _).mpr ⟨by simp [optMatch], h3a⟩
              | some kvs =>
                obtain ⟨m, hm, hmk⟩ := h3b
                cases r3 with
                | Err e => simp at hm
                | Ok m' =>
                  simp only [okPart_Ok, Option.some.injEq] at hm
                  subst hm
                  simp only [bind_ok]
                  refine (WP.spec_ok _).mpr ⟨?_, h3a⟩
                  simp only [okPart_Ok, optMatch, ChangeUserMore.Matches, ChangeUserMore.of]
                  exact ⟨by rw [h1a, hon], hoc, hmk⟩
  · rw [ite_eq_right hl] at h1
    obtain ⟨h1a, hb1⟩ := h1
    have hnl : (↑buf : List U8).length < 2 := by simp [Slice.length] at hl; omega
    simp only [hnl, ite_true]
    cases r1 with
    | Ok _ => simp at h1a
    | Err e =>
      simp only [CoreOpsTry.branch, bind_ok, from_residual_eq]
      exact (WP.spec_ok _).mpr ⟨by simp [optMatch], by rw [hb1]⟩

/-- `MySerialize for ComChangeUserMoreData`: appends `changeUserMoreEnc`: **the attributes are always written** (the single byte `0` if there are none, by `Trusted.connectAttrsEntries_new`), whatever the flags. -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUserMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD []) ⦄ := by
  unfold packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [changeUserMoreEnc, ChangeUserMore.of, List.length_append, PBUtil.length_leBytes] at h ⊢
  step with PCSUtil.rawint_u16_serialize as ⟨b1, hb1⟩
  have l1 : b1.length = buf.length + 2 := by simp [alloc.vec.Vec.length, hb1, PBUtil.length_leBytes]
  cases hap : self.auth_plugin with
  | none =>
    simp only [hap, Option.map_none, List.length_nil, add_zero] at h ⊢
    apply WP.spec_mono (serialize_change_user_connect_attrs_spec _ b1 (by rw [l1]; omega))
    intro r hr; rw [hr, hb1]; simp
  | some p =>
    simp only [hap, Option.map_some, List.length_append, List.length_singleton] at h ⊢
    step with packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec p b1 (by rw [l1]; omega) as ⟨b2, hb2⟩
    have l2 : b2.length = buf.length + 2 + (authPluginName p).length + 1 := by
      simp [alloc.vec.Vec.length, hb2, hb1, PBUtil.length_leBytes]; omega
    apply WP.spec_mono (serialize_change_user_connect_attrs_spec _ b2 (by rw [l2]; omega))
    intro r hr; rw [hr, hb2, hb1]; simp

/-- Round trip, with `ChangeUserMore.Compatible` flags (in particular `CLIENT_CONNECT_ATTRS`: otherwise the always-written attributes are left unread). -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (m : ChangeUserMore) (kvs : List (List U8 × List U8))
    (hc : ChangeUserMore.Compatible caps.val m) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = changeUserMoreEnc m kvs ++ tail) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ md, okPart r = some md ∧ ChangeUserMore.Matches md m (some kvs)) ∧ rest.val = tail ⦄ := by
  have hl : (attrsEnc kvs).length < 2 ^ 64 := by
    have := lt_two_pow_64_of_le_max (n := buf.val.length) (by scalar_tac)
    rw [h] at this; simp [changeUserMoreEnc] at this; omega
  have e := changeUserMoreRead_enc caps.val m kvs tail hc hl
  rw [← h] at e
  apply WP.spec_mono (packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec h64 caps buf)
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  rw [e] at h1 h2
  refine ⟨?_, h2⟩
  cases hr : okPart r with
  | none => rw [hr] at h1; simp [optMatch] at h1
  | some md => rw [hr] at h1; exact ⟨md, rfl, h1⟩

end mysql_common
