import Defs
import Proofs.Defs.Lemmas
import Proofs.Util.RawBytesSeq

/-! Facts about the connection-phase definitions (`lean/Defs/Connection.lean`) (spec file:
`Specs/DefsConn.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

namespace ConnHS

theorem hasFlag_two_pow (x k : Nat) : hasFlag x (2 ^ k) = decide (x / 2 ^ k % 2 = 1) := by
  unfold hasFlag
  have : x &&& 2 ^ k = if x.testBit k then 2 ^ k else 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : k = j
    · subst hj; split <;> simp_all
    · split <;> simp [hj]
  rw [this, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x / 2 ^ k % 2 = 1 <;> simp [h]

theorem nulStrRead_nulStr (s t : List U8) (h : NoNul s) : nulStrRead (nulStr s ++ t) = (some s, t) := by
  have hb : beforeZero s = s := PBUtil.beforeZero_of_all s h
  have hz : beforeZero (s ++ byte 0 :: t) = s := beforeZero_append_zero s t h
  unfold nulStrRead nulStr
  rw [hb]
  have hn : hasNul (s ++ byte 0 :: t) = true := by
    simp [hasNul]; right; left; rfl
  simp only [List.append_assoc, List.singleton_append, hn, hz]
  simp

theorem statusRead_lt {n : Nat} (h : statusRead n = some n) : n < 2 ^ 16 := by
  unfold statusRead at h
  split_ifs at h with h1
  have : n &&& statusFlagsAll ≤ statusFlagsAll := Nat.and_le_right
  rw [h1] at this
  simp [statusFlagsAll] at this; omega

theorem handshakeEnc_split (hs : Handshake) (tail : List U8) (h1 : hs.scramble1.length = 8) :
    ∃ blk rest, blk.length = 31 ∧ handshakeEnc hs ++ tail = byte hs.protocolVersion :: (nulStr hs.serverVersion ++ (blk ++ rest)) ∧
      rest = (hs.scramble2.map (·.take 247)).getD [] ++ ((hs.pluginName.map nulStr).getD [] ++ tail) ∧
      (blk.drop 13).take 2 = leBytes 2 hs.capsLower ∧ (blk.drop 16).take 2 = leBytes 2 hs.status ∧
      (blk.drop 18).take 2 = leBytes 2 (hs.capsUpper / 2 ^ 16) ∧ blk.getD 20 (byte 0) = byte (handshakeLenByte hs) ∧
      (blk.drop 0).take 4 = leBytes 4 hs.connectionId ∧ (blk.drop 4).take 8 = hs.scramble1 ∧
      (blk.drop 15).take 1 = [byte hs.collation] ∧ (blk.drop 20).take 1 = [byte (handshakeLenByte hs)] ∧
      (blk.drop 27).take 4 = leBytes 4 hs.mariadbCaps := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7, hs.scramble1 = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    match h : hs.scramble1, h1 with
    | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  refine ⟨leBytes 4 hs.connectionId ++ hs.scramble1 ++ [byte 0] ++ leBytes 2 hs.capsLower ++ [byte hs.collation] ++ leBytes 2 hs.status
    ++ leBytes 2 (hs.capsUpper / 2 ^ 16) ++ [byte (handshakeLenByte hs)] ++ List.replicate 6 (byte 0) ++ leBytes 4 hs.mariadbCaps, _, ?_, ?_, rfl, ?_⟩
  · simp [PBUtil.length_leBytes, h1]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, s2, pn⟩ := hs
    cases s2 <;> cases pn <;> simp [handshakeEnc]
  · simp [ha, leBytes, List.replicate]

theorem dt_app (blk rest : List U8) (i k : Nat) (h : i + k ≤ blk.length) :
    ((blk ++ rest).drop i).take k = (blk.drop i).take k := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem getD_app (blk rest : List U8) (i : Nat) (d : U8) (h : i < blk.length) :
    (blk ++ rest).getD i d = blk.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem handshakeLenByte_eq (hs : Handshake) (s : List U8)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s) :
    handshakeLenByte hs = min s.length 247 + 8 := by
  simp [handshakeLenByte, hpa, hs2]

/-- The body of `attrsEnc`. -/
def attrsBody (kvs : List (List U8 × List U8)) : List U8 :=
  (kvs.map (fun kv => lenencStr kv.1 ++ lenencStr kv.2)).flatten

theorem lenencStr_ne_nil (s : List U8) : lenencStr s ≠ [] := by
  unfold lenencStr lenencInt; split_ifs <;> simp

theorem attrsBody_length (kvs : List (List U8 × List U8)) : kvs.length ≤ (attrsBody kvs).length := by
  induction kvs with
  | nil => simp
  | cons kv kvs ih =>
    simp only [attrsBody, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    have := List.length_pos_iff.mpr (lenencStr_ne_nil kv.1)
    omega

theorem attrEntriesAux_body (kvs : List (List U8 × List U8)) (fuel : Nat) (hf : kvs.length ≤ fuel)
    (h : (attrsBody kvs).length < 2 ^ 64) : attrEntriesAux fuel (attrsBody kvs) = some kvs := by
  induction kvs generalizing fuel with
  | nil => cases fuel <;> simp [attrsBody, attrEntriesAux]
  | cons kv kvs ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hb : attrsBody (kv :: kvs) = lenencStr kv.1 ++ (lenencStr kv.2 ++ attrsBody kvs) := by
      simp [attrsBody]
    rw [hb] at h ⊢
    simp only [List.length_append] at h
    obtain ⟨b, bs, hc⟩ : ∃ b bs, lenencStr kv.1 ++ (lenencStr kv.2 ++ attrsBody kvs) = b :: bs := by
      cases hh : lenencStr kv.1 with
      | nil => exact absurd hh (lenencStr_ne_nil _)
      | cons b bs => exact ⟨b, _, rfl⟩
    rw [hc]
    simp only [attrEntriesAux]
    rw [← hc]
    have l1 : kv.1.length < 2 ^ 64 := by simp [lenencStr] at h; omega
    have l2 : kv.2.length < 2 ^ 64 := by simp [lenencStr] at h; omega
    rw [checkedLenencStr_lenencStr _ _ l1]
    simp only
    rw [checkedLenencStr_lenencStr _ _ l2]
    simp only
    rw [ih f (by simp at hf; omega) (by omega)]
    simp

end ConnHS

open ConnHS

/-- A known plugin's name names it. -/
theorem knownPlugin_authPluginName (p : packets.AuthPlugin) (h : isOtherPlugin p = false) :
    knownPlugin (authPluginName p) = some p := by
  cases p <;> simp_all [isOtherPlugin] <;> rfl

/-- The plugin named `n` has the name `n`. -/
theorem IsPluginNamed.authPluginName {n : List U8} {r : packets.AuthPlugin} (h : IsPluginNamed n r) : authPluginName r = n := by
  unfold IsPluginNamed at h
  split at h
  · rename_i p hp
    subst h
    unfold knownPlugin at hp
    have := List.find?_some hp
    simpa using this
  · obtain ⟨c, rfl, hc⟩ := h
    simpa [Defs.authPluginName] using hc

/-- A plugin named by some bytes is in normal form. -/
theorem IsPluginNamed.canonical {n : List U8} {r : packets.AuthPlugin} (h : IsPluginNamed n r) : PluginCanonical r := by
  unfold PluginCanonical; rw [IsPluginNamed.authPluginName h]; exact h

/-- `from_bytes` gives the plugin named by the bytes without one trailing `0`, in normal form. -/
theorem PluginFromBytes.named {n : List U8} {r : packets.AuthPlugin} (h : PluginFromBytes n r) :
    IsPluginNamed (dropTrailingNul n) r ∧ PluginCanonical r := by
  have hn : IsPluginNamed (dropTrailingNul n) r := by
    unfold PluginFromBytes at h
    unfold IsPluginNamed
    split at h <;> rename_i heq
    · exact h
    · obtain ⟨s, rfl, hs⟩ := h
      exact ⟨_, rfl, hs⟩
  exact ⟨hn, hn.canonical⟩

/-- The crate's scramble length is the protocol's for a length byte below 128. -/
theorem scramble2LenCrate_of_lt (b : Nat) (h : b < 128) : scramble2LenCrate b = scramble2Len b := by
  simp [scramble2LenCrate, scramble2Len, h]

/-- **The crate's scramble length is wrong for a length byte of 136 or more**: 13 instead of `b - 8`. -/
theorem scramble2LenCrate_ne (b : Nat) (h1 : 136 ≤ b) (h2 : b < 256) : scramble2LenCrate b = 13 ∧ scramble2Len b = b - 8 ∧ b - 8 ≠ 13 := by
  simp [scramble2LenCrate, scramble2Len, show ¬ b < 128 by omega]; omega

/-- **The crate cannot read its own handshake** with `CLIENT_SECURE_CONNECTION`, `CLIENT_PLUGIN_AUTH` and a scramble of 120–127 bytes: the written length byte `8 + n` is in `128..135`, and the reader panics. -/
theorem handshakePanics_handshakeEnc (hs : Handshake) (s : List U8) (tail : List U8) (hv : NoNul hs.serverVersion)
    (hst : statusRead hs.status = some hs.status) (hl : hs.capsLower < 2 ^ 16)
    (hsec : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s)
    (hn : 120 ≤ s.length ∧ s.length ≤ 127) (h1 : hs.scramble1.length = 8) :
    handshakePanics (handshakeEnc hs ++ tail) := by
  have H := handshakeEnc_split hs tail h1
  obtain ⟨blk, rest, H⟩ := H
  have hbl := H.1
  have he := H.2.1
  have hcl := H.2.2.2.1
  have hst' := H.2.2.2.2.1
  have hlb := H.2.2.2.2.2.2.1
  clear H
  rw [he]
  unfold handshakePanics
  simp only [nulStrRead_nulStr _ _ hv]
  have hs16 := statusRead_lt hst
  have hb := handshakeLenByte_eq hs s hpa hs2
  refine ⟨by simp [hbl], ?_, ?_, ?_, ?_⟩
  · rw [dt_app _ _ _ _ (by omega), hst', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt (by omega), hst]; simp
  · rw [dt_app _ _ _ _ (by omega), hcl, PBUtil.leNat_leBytes, Nat.mod_eq_of_lt (by omega), hsec]
  · rw [getD_app _ _ _ _ (by omega), hlb, PBUtil.byte_val, hb]; omega
  · rw [getD_app _ _ _ _ (by omega), hlb, PBUtil.byte_val, hb]; omega

/-- **The crate misreads its own handshake** with `CLIENT_SECURE_CONNECTION`, `CLIENT_PLUGIN_AUTH` and a scramble of 128–247 bytes, in every build: the written length byte `8 + n` is in `136..255`, there is no panic, and the reader takes only the first 13 scramble bytes (silently; the rest becomes part of the plugin name). -/
theorem handshakeEnc_misread (hs : Handshake) (s : List U8) (tail : List U8) (hv : NoNul hs.serverVersion)
    (hst : statusRead hs.status = some hs.status) (hl : hs.capsLower < 2 ^ 16)
    (hsec : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s)
    (hn : 128 ≤ s.length ∧ s.length ≤ 247) (h1 : hs.scramble1.length = 8) :
    136 ≤ handshakeLenByte hs ∧ handshakeLenByte hs < 256 ∧ ¬ handshakePanics (handshakeEnc hs ++ tail) ∧
      (handshakeRead (handshakeEnc hs ++ tail)).1.map (·.scramble2) = some (some (s.take 13)) := by
  have H := handshakeEnc_split hs tail h1
  obtain ⟨blk, rest, H⟩ := H
  have hbl := H.1
  have he := H.2.1
  have hrest := H.2.2.1
  have hcl := H.2.2.2.1
  have hst' := H.2.2.2.2.1
  have hlb := H.2.2.2.2.2.2.1
  have hlb1 := H.2.2.2.2.2.2.2.2.2.2.1
  clear H
  have hs16 := statusRead_lt hst
  have hb := handshakeLenByte_eq hs s hpa hs2
  have hbv : (byte (handshakeLenByte hs)).val = handshakeLenByte hs := by
    rw [PBUtil.byte_val, hb]; omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [he]
    unfold handshakePanics
    simp only [nulStrRead_nulStr _ _ hv]
    rintro ⟨-, -, -, -, h5⟩
    rw [getD_app _ _ _ _ (by omega), hlb, hbv] at h5
    omega
  · rw [he]
    unfold handshakeRead
    simp only [nulStrRead_nulStr _ _ hv]
    have hl31 : ¬ (blk ++ rest).length < 31 := by simp; omega
    have ht : (blk ++ rest).take 31 = blk := List.take_left' hbl
    have hd : (blk ++ rest).drop 31 = rest := List.drop_left' hbl
    have hlen : leNat ((blk.drop 20).take 1) = handshakeLenByte hs := by
      rw [hlb1]; simp [leNat, hbv]
    have hstat : leNat ((blk.drop 16).take 2) = hs.status := by
      rw [hst', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt (by omega)]
    have hcaps : leNat ((blk.drop 13).take 2) = hs.capsLower := by
      rw [hcl, PBUtil.leNat_leBytes, Nat.mod_eq_of_lt (by omega)]
    have hrs : rest = s ++ ((hs.pluginName.map nulStr).getD [] ++ tail) := by
      rw [hrest, hs2]; simp [List.take_of_length_le (show s.length ≤ 247 by omega)]
    simp only [hl31, ite_false, ht, hd, hlen, hstat, hcaps, hst, hsec, ite_true]
    have h13 : scramble2LenCrate (handshakeLenByte hs) = 13 := by
      simp only [scramble2LenCrate]; rw [ite_eq_right_iff.mpr (fun h => by omega)]
    have hr13 : ¬ rest.length < 13 := by rw [hrs]; simp; omega
    simp only [h13, hr13, reduceCtorEq, ite_false]
    rw [hrs, List.take_append_of_le_length (show 13 ≤ s.length by omega)]
    simp

/-- The attributes reader inverts `attrsEnc`. -/
theorem connectAttrsRead_attrsEnc (kvs : List (List U8 × List U8)) (tail : List U8) (h : (attrsEnc kvs).length < 2 ^ 64) :
    connectAttrsRead (attrsEnc kvs ++ tail) = (some kvs, tail) := by
  have he : attrsEnc kvs = lenencInt (attrsBody kvs).length ++ attrsBody kvs := rfl
  rw [he] at h ⊢
  have hl : (attrsBody kvs).length < 2 ^ 64 := by simp at h; omega
  unfold connectAttrsRead
  rw [List.append_assoc, checkedLenencInt_lenencInt _ _ hl]
  simp only [List.length_append, show ¬ ((attrsBody kvs).length + tail.length < (attrsBody kvs).length) by omega,
    ite_false, List.take_left', List.drop_left']
  rw [attrEntriesAux_body _ _ (attrsBody_length kvs) hl]

/-- An example of `VERSION_RE`: `8.0.32-0ubuntu0.22.04.2` is version 8.0.32. -/
theorem versionReMatch_example :
    digitsTriple (versionReMatch (utf8 "8.0.32-0ubuntu0.22.04.2")) = some (8, 0, 32) := by
  decide

/-- An example of `MARIADB_VERSION_RE`: `5.5.5-10.6.12-MariaDB-log` is MariaDB 10.6.12 (the `5.5.5-` prefix is skipped); a MySQL version string does not match. -/
theorem mariadbVersionReMatch_example :
    digitsTriple (mariadbVersionReMatch (utf8 "5.5.5-10.6.12-MariaDB-log")) = some (10, 6, 12) ∧
      mariadbVersionReMatch (utf8 "8.0.32") = none := by
  decide

/-- Example: MySQL's own handshake scramble is read as 8 + 12 bytes of nonce (the 13th, a `0`, is dropped). -/
theorem handshakeNonce_mysql (s1 s2 : List U8) (h1 : s1.length = 8) (h2 : s2.length = 12) :
    handshakeNonce s1 (some (s2 ++ [byte 0])) = s1 ++ s2 := by
  unfold handshakeNonce dropTrailingNul
  simp [PBUtil.byte_val, h1, h2]

end Defs
