import Defs
import Proofs.Util.ConnAuth
import Proofs.Packets.ComChangeUserMoreData

/-! Statements for `struct ComChangeUser and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil
open core.result.Result.Insts

namespace mysql_common

private theorem parse_u8_bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = checkedLenPrefixed 1 buf.val)
    (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

private theorem more_data_spec (h64 : Target64) (flags : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.parse_change_user_more_data flags buf ⦃ r rest =>
      if buf.val = [] then okPart r = some none ∧ rest = buf
      else optMatch (fun (o : Option packets.ComChangeUserMoreData) vk => ∃ m, o = some m ∧ ChangeUserMore.Matches m vk.1 vk.2)
          (okPart r) (changeUserMoreRead flags.val buf.val).1 ∧
        rest.val = (changeUserMoreRead flags.val buf.val).2 ⦄ := by
  unfold packets.parse_change_user_more_data
  step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
  split
  · rename_i hbt
    have : buf.val = [] := hb.mp hbt
    exact (WP.spec_ok _).mpr (by simp [this])
  · rename_i hbf
    have hne : buf.val ≠ [] := fun h => hbf (hb.mpr h)
    rw [io.ParseBuf.parse_of_size_none _ _ _ (by
      simp [packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE])]
    apply WP.spec_bind (packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec h64 flags buf)
    rintro ⟨r, rest⟩ ⟨h1, h2⟩
    simp only [hne, ite_false]
    cases r with
    | Ok m =>
      refine (WP.spec_ok _).mpr ⟨?_, h2⟩
      simp only [okPart_Ok] at h1 ⊢
      cases hc : (changeUserMoreRead flags.val buf.val).1 with
      | none => rw [hc] at h1; simp [optMatch] at h1
      | some vk => rw [hc] at h1; exact ⟨m, rfl, h1⟩
    | Err e =>
      refine (WP.spec_ok _).mpr ⟨?_, h2⟩
      simp only [okPart_Err] at h1 ⊢
      cases hc : (changeUserMoreRead flags.val buf.val).1 with
      | none => simp [optMatch]
      | some vk => rw [hc] at h1; simp [optMatch] at h1

private theorem checkedLenPrefixed_one (a rest : List U8) (ha : a.length ≤ 255) :
    checkedLenPrefixed 1 (byte a.length :: (a ++ rest)) = (some a, rest) := by
  have hb : (byte a.length).val = a.length := by rw [PBUtil.byte_val]; omega
  simp [checkedLenPrefixed, readLE, leNat, hb]

private theorem changeUserRead_enc (caps : Nat) (v : ChangeUser) (kvs : List (List U8 × List U8))
    (hc : ChangeUser.Compatible caps v) (tail : List U8) (ht : v.moreData = none → tail = [])
    (hl : (attrsEnc kvs).length < 2 ^ 64) :
    changeUserRead caps (changeUserEnc v kvs ++ tail) = (some (v, v.moreData.map (fun _ => kvs)), tail) := by
  obtain ⟨u, a, d, mo⟩ := v
  obtain ⟨hu, ha, hd, hm⟩ := hc
  simp only at hu ha hd hm ht ⊢
  have h17 : (byte 0x11).val = 17 := by rw [PBUtil.byte_val]
  cases mo with
  | none =>
    have := ht rfl
    subst this
    have e : changeUserEnc ⟨u, a, d, none⟩ kvs ++ [] =
        byte 0x11 :: (nulStr u ++ (byte a.length :: (a ++ (nulStr d ++ [])))) := by
      simp [changeUserEnc, Nat.min_eq_left ha, List.take_of_length_le ha]
    rw [e]
    simp only [changeUserRead, h17, ne_eq, not_true_eq_false, ite_false]
    rw [nulStrRead_nulStr u _ hu]
    simp only
    rw [checkedLenPrefixed_one a _ ha]
    simp only
    rw [nulStrRead_nulStr d _ hd]
    simp
  | some m =>
    have e : changeUserEnc ⟨u, a, d, some m⟩ kvs ++ tail =
        byte 0x11 :: (nulStr u ++ (byte a.length :: (a ++ (nulStr d ++ (changeUserMoreEnc m kvs ++ tail))))) := by
      simp [changeUserEnc, Nat.min_eq_left ha, List.take_of_length_le ha]
    rw [e]
    simp only [changeUserRead, h17, ne_eq, not_true_eq_false, ite_false]
    rw [nulStrRead_nulStr u _ hu]
    simp only
    rw [checkedLenPrefixed_one a _ ha]
    simp only
    rw [nulStrRead_nulStr d _ hd]
    have hne : changeUserMoreEnc m kvs ++ tail ≠ [] := by
      simp [changeUserMoreEnc, PBUtil.length_leBytes, ← List.length_eq_zero_iff]
    simp only [hne, ite_false]
    rw [changeUserMoreRead_enc caps m kvs tail (hm m rfl) hl]
    simp

/-- `new`: empty user, auth data and database, no tail. -/
theorem packets.ComChangeUser.new_spec :
    packets.ComChangeUser.new ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄ := by
  unfold packets.ComChangeUser.new misc.raw.int.ConstU8.new
  step*
  simp [ChangeUser.of, *]

/-- `with_user`: the given user (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_user_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (user : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, user = some x → into.into x = ok c) :
    packets.ComChangeUser.with_user into self user ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with user := (user.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  unfold packets.ComChangeUser.with_user
  cases hx : user with
  | none =>
    simp only
    step with rawbytes_default_spec as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]
  | some x =>
    simp only
    step with rawbytes_new_spec _ _ x c (h x hx) as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]

/-- `with_database`: the given database (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_database_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (database : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, database = some x → into.into x = ok c) :
    packets.ComChangeUser.with_database into self database ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with database := (database.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  unfold packets.ComChangeUser.with_database
  cases hx : database with
  | none =>
    simp only
    step with rawbytes_default_spec as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]
  | some x =>
    simp only
    step with rawbytes_new_spec _ _ x c (h x hx) as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]

/-- `with_auth_plugin_data`: the given auth data (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_auth_plugin_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (auth_plugin_data : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, auth_plugin_data = some x → into.into x = ok c) :
    packets.ComChangeUser.with_auth_plugin_data into self auth_plugin_data ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with authData := (auth_plugin_data.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  unfold packets.ComChangeUser.with_auth_plugin_data
  cases hx : auth_plugin_data with
  | none =>
    simp only
    step with rawbytes_default_spec as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]
  | some x =>
    simp only
    step with rawbytes_new_spec _ _ x c (h x hx) as ⟨rb, hrb⟩
    simp [ChangeUser.of, hrb]

/-- `with_more_data`: replaces the tail. -/
theorem packets.ComChangeUser.with_more_data_eq (self : packets.ComChangeUser) (more_data : Option packets.ComChangeUserMoreData) :
    packets.ComChangeUser.with_more_data self more_data = ok { self with more_data := more_data } := by
  rfl

/-- `into_owned`: the same fields; plugins stay known or `Other`, maps become `connectAttrsIntoOwned` of themselves. -/
theorem packets.ComChangeUser.into_owned_spec (self : packets.ComChangeUser) :
    packets.ComChangeUser.into_owned self ⦃ p =>
      ChangeUser.of p = ChangeUser.of self ∧
        p.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin, m.connect_attributes)) =
          self.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin,
            m.connect_attributes.map Trusted.connectAttrsIntoOwned)) ⦄ := by
  unfold packets.ComChangeUser.into_owned
  step with rawbytes_into_owned_spec as ⟨u, hu⟩
  step with rawbytes_into_owned_spec as ⟨a, ha⟩
  step with rawbytes_into_owned_spec as ⟨d, hd⟩
  cases hm : self.more_data with
  | none => simp [ChangeUser.of, hu, ha, hd, hm]
  | some md =>
    simp only
    step with packets.ComChangeUserMoreData.into_owned_spec as ⟨md', h1, h2, h3⟩
    simp [ChangeUser.of, hu, ha, hd, hm, h1, h2, h3]

/-- `Default`: `new()`. -/
theorem packets.ComChangeUser.Insts.CoreDefaultDefault.default_spec :
    packets.ComChangeUser.Insts.CoreDefaultDefault.default ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄ := by
  unfold packets.ComChangeUser.Insts.CoreDefaultDefault.default
  exact packets.ComChangeUser.new_spec

/-- `MyDeserialize for ComChangeUser`: `SIZE` is `None`. -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  simp [packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE]

/-- `MyDeserialize for ComChangeUser`: total; `changeUserRead` with the capability flags (the fields, the tail's plugin in normal form and its map built from the wire entries; errors; what is left). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun p vk => ChangeUser.Matches p vk.1 vk.2) (okPart r) (changeUserRead caps.val buf.val).1 ∧
        rest.val = (changeUserRead caps.val buf.val).2 ⦄ := by
  unfold packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize
  step with header_parse_spec 17#u8 packets.InvalidComChangeUserHeader.Insts.CoreErrorError
    packets.InvalidComChangeUserHeader.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    rw [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e =>
      simp only [branch_err, bind_ok, from_residual_eq]
      exact (WP.spec_ok _).mpr ⟨by simp [changeUserRead, optMatch], by simp [changeUserRead, hb1, hb]⟩
  | cons b t =>
    rw [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    simp only [changeUserRead]
    cases r with
    | Err e =>
      have hne : b.val ≠ 17 := by simpa using hr
      simp only [branch_err, bind_ok, from_residual_eq]
      exact (WP.spec_ok _).mpr ⟨by simp [hne, optMatch], by simp [hne, hb1]⟩
    | Ok v =>
      have heq : b.val = 17 := by simpa using hr
      simp only [heq, ne_eq, not_true_eq_false, ite_false]
      simp only [branch_ok, bind_ok]
      step with parse_null_bytes_spec as ⟨r2, buf2, h2⟩
      rw [hb1] at h2
      cases hn : nulStrRead t with
      | mk ou rr1 =>
        rw [hn] at h2
        cases r2 with
        | Err e =>
          simp only [okPart_Err, Option.map_none, Prod.mk.injEq] at h2
          obtain ⟨hou, hrr⟩ := h2
          subst hou
          simp only [branch_err, bind_ok, from_residual_eq]
          exact (WP.spec_ok _).mpr ⟨by simp [optMatch], by simp [hrr]⟩
        | Ok rb =>
          simp only [okPart_Ok, Option.map_some, Prod.mk.injEq] at h2
          obtain ⟨hou, hrr⟩ := h2
          subst hou
          simp only [branch_ok, bind_ok]
          step with parse_u8_bytes_spec as ⟨r3, buf3, h3⟩
          rw [hrr] at h3
          cases hc : checkedLenPrefixed 1 rr1 with
          | mk oa rr2 =>
            rw [hc] at h3
            cases r3 with
            | Err e =>
              simp only [okPart_Err, Option.map_none, Prod.mk.injEq] at h3
              obtain ⟨hoa, hrr2⟩ := h3
              subst hoa
              simp only [branch_err, bind_ok, from_residual_eq]
              exact (WP.spec_ok _).mpr ⟨by simp [optMatch], by simp [hrr2]⟩
            | Ok rb1 =>
              simp only [okPart_Ok, Option.map_some, Prod.mk.injEq] at h3
              obtain ⟨hoa, hrr2⟩ := h3
              subst hoa
              simp only [branch_ok, bind_ok]
              step with parse_null_bytes_spec as ⟨r4, buf4, h4⟩
              rw [hrr2] at h4
              cases hd : nulStrRead rr2 with
              | mk od rr3 =>
                rw [hd] at h4
                cases r4 with
                | Err e =>
                  simp only [okPart_Err, Option.map_none, Prod.mk.injEq] at h4
                  obtain ⟨hod, hrr3⟩ := h4
                  subst hod
                  simp only [branch_err, bind_ok, from_residual_eq]
                  exact (WP.spec_ok _).mpr ⟨by simp [optMatch], by simp [hrr3]⟩
                | Ok rb2 =>
                  simp only [okPart_Ok, Option.map_some, Prod.mk.injEq] at h4
                  obtain ⟨hod, hrr3⟩ := h4
                  subst hod
                  simp only [branch_ok, bind_ok]
                  step with more_data_spec h64 as ⟨r5, buf5, h5⟩
                  rw [hrr3] at h5
                  by_cases he : rr3 = []
                  · rw [ite_eq_left he] at h5
                    obtain ⟨h5a, h5b⟩ := h5
                    cases r5 with
                    | Err e => simp at h5a
                    | Ok o =>
                      simp only [okPart_Ok, Option.some.injEq] at h5a
                      subst h5a
                      simp only [branch_ok, bind_ok, he, ite_true]
                      refine (WP.spec_ok _).mpr ⟨?_, by rw [h5b, ← he, hrr3]⟩
                      simp [optMatch, ChangeUser.Matches, ChangeUser.of]
                  · rw [ite_eq_right he] at h5
                    simp only [he, ite_false]
                    obtain ⟨h5a, h5b⟩ := h5
                    cases hm : changeUserMoreRead caps.val rr3 with
                    | mk om rr4 =>
                      rw [hm] at h5a h5b
                      cases om with
                      | none =>
                        cases r5 with
                        | Ok o => simp [optMatch] at h5a
                        | Err e =>
                          simp only [branch_err, bind_ok, from_residual_eq]
                          exact (WP.spec_ok _).mpr ⟨by simp [optMatch], h5b⟩
                      | some mk =>
                        obtain ⟨m, kvs⟩ := mk
                        cases r5 with
                        | Err e => simp [optMatch] at h5a
                        | Ok o =>
                          simp only [okPart_Ok, optMatch] at h5a
                          obtain ⟨md, rfl, hmd⟩ := h5a
                          simp only [branch_ok, bind_ok]
                          refine (WP.spec_ok _).mpr ⟨?_, h5b⟩
                          simp only [okPart_Ok, optMatch, ChangeUser.Matches, ChangeUser.of]
                          refine ⟨by simp [hmd.1], hmd.2.1, hmd.2.2⟩

/-- `MySerialize for ComChangeUser`: appends `changeUserEnc` of the fields, with the entries of the tail's map in its iteration order (none if it has no map: the crate writes an empty map, whose attributes are the single byte `0` by `Trusted.connectAttrsEntries_new`). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUser) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD []) ⦄ := by
  unfold packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [changeUserEnc, ChangeUser.of, nulStr, List.length_append, List.length_cons, List.length_take,
    List.length_nil] at h ⊢
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, hb1⟩
  have l1 : b1.length = buf.length + 1 := by simp [alloc.vec.Vec.length, hb1]
  apply WP.spec_bind (Pₘ := fun b2 : alloc.vec.Vec U8 => b2.val = b1.val ++ beforeZero (cowList self.user.1) ++ [byte 0])
  · apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro t ht
    apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec t b1 ?_)
    · intro b hb; rw [hb, ht]
    · rw [l1, ht]; omega
  intro b2 hb2
  have l2 : b2.length = buf.length + 1 + (beforeZero (cowList self.user.1)).length + 1 := by
    simp [alloc.vec.Vec.length, hb2, hb1]; omega
  apply WP.spec_bind (Pₘ := fun b3 : alloc.vec.Vec U8 => b3.val = b2.val ++
    byte (min (cowList self.auth_plugin_data.1).length 255) :: (cowList self.auth_plugin_data.1).take 255)
  · apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro t ht
    apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec t b2 ?_)
    · intro b hb; rw [hb, ht]; simp [Slice.length, ht]
    · have : t.length = (cowList self.auth_plugin_data.1).length := by simp [Slice.length, ht]
      rw [l2, this]; omega
  intro b3 hb3
  have l3 : b3.length = buf.length + 1 + (beforeZero (cowList self.user.1)).length + 1 + 1 +
      min (cowList self.auth_plugin_data.1).length 255 := by
    simp [alloc.vec.Vec.length, hb3, hb2, hb1]; omega
  apply WP.spec_bind (Pₘ := fun b4 : alloc.vec.Vec U8 => b4.val = b3.val ++ beforeZero (cowList self.database.1) ++ [byte 0])
  · apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
    intro t ht
    apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec t b3 ?_)
    · intro b hb; rw [hb, ht]
    · rw [l3, ht]; omega
  intro b4 hb4
  have l4 : b4.length = buf.length + 1 + (beforeZero (cowList self.user.1)).length + 1 + 1 +
      min (cowList self.auth_plugin_data.1).length 255 + (beforeZero (cowList self.database.1)).length + 1 := by
    simp [alloc.vec.Vec.length, hb4, hb3, hb2, hb1]; omega
  cases hm : self.more_data with
  | none =>
    refine (WP.spec_ok _).mpr ?_
    rw [hb4, hb3, hb2, hb1]; simp; rfl
  | some md =>
    simp only [hm, Option.map_some, Option.bind_some] at h ⊢
    apply WP.spec_mono (packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec md b4 (by rw [l4]; omega))
    intro r hr
    rw [hr, hb4, hb3, hb2, hb1]; simp; rfl

/-- Round trip: a `ChangeUser.Compatible` request written by `changeUserEnc` reads back with the same fields, its tail's map built from the written entries. Without a tail nothing may follow (any byte would be read as a tail). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (v : ChangeUser) (kvs : List (List U8 × List U8))
    (hc : ChangeUser.Compatible caps.val v) (tail : List U8) (ht : v.moreData = none → tail = [])
    (buf : io.ParseBuf) (h : buf.val = changeUserEnc v kvs ++ tail) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ ChangeUser.Matches p v (v.moreData.map (fun _ => kvs))) ∧ rest.val = tail ⦄ := by
  have hl : (attrsEnc kvs).length < 2 ^ 64 ∨ v.moreData = none := by
    cases hm : v.moreData with
    | none => exact Or.inr rfl
    | some m =>
      left
      have := lt_two_pow_64_of_le_max (n := buf.val.length) (by scalar_tac)
      rw [h] at this; simp [changeUserEnc, hm, changeUserMoreEnc] at this; omega
  have e : changeUserRead caps.val buf.val = (some (v, v.moreData.map (fun _ => kvs)), tail) := by
    rw [h]
    rcases hl with hl | hm
    · exact changeUserRead_enc caps.val v kvs hc tail ht hl
    · have := changeUserRead_enc caps.val v [] hc tail ht (by simp [attrsEnc, lenencInt])
      have e2 : changeUserEnc v kvs = changeUserEnc v [] := by simp [changeUserEnc, hm]
      rw [e2, this]; simp [hm]
  apply WP.spec_mono (packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec h64 caps buf)
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  rw [e] at h1 h2
  refine ⟨?_, h2⟩
  cases hr : okPart r with
  | none => rw [hr] at h1; simp [optMatch] at h1
  | some p => rw [hr] at h1; exact ⟨p, rfl, h1⟩

end mysql_common
