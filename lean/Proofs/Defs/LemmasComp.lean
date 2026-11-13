import Defs
import Proofs.Util.CompCodec

/-! Sanity lemmas about `Defs/Compression.lean` (recalled in `Specs/DefsComp.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace Defs

open mysql_common.CompCodec

/-- A compressed-packet header has 7 bytes and reads back its fields (lengths below `2^24`). -/
theorem compHeaderRead_compHeader (cl seq pl : Nat) (hcl : cl < 2 ^ 24) (hpl : pl < 2 ^ 24) (t : List U8) :
    (compHeader cl seq pl).length = 7 ∧ compHeaderRead (compHeader cl seq pl ++ t) = (cl, byte seq, pl) := by
  have h3 := PBUtil.length_leBytes 3 cl
  have h3' := PBUtil.length_leBytes 3 pl
  have k1 := PBUtil.leNat_leBytes 3 cl
  have k2 := PBUtil.leNat_leBytes 3 pl
  refine ⟨by simp [compHeader, h3, h3'], ?_⟩
  simp only [compHeaderRead, compHeader]
  generalize leBytes 3 cl = A at h3 k1
  generalize leBytes 3 pl = B at h3' k2
  match A, B, h3, h3' with
  | [a1, a2, a3], [b1, b2, b3], _, _ =>
    simp only [List.cons_append, List.nil_append, List.take_succ_cons,
      List.take_zero, List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero, k1, k2,
      Prod.mk.injEq, true_and]
    constructor <;> apply Nat.mod_eq_of_lt <;> omega

/-- `chunksOf n` (for `n > 0`) cuts `bs` into non-empty pieces of at most `n` bytes that concatenate back to `bs`; all but the last have exactly `n` bytes, and there are `⌈|bs| / n⌉` of them. -/
theorem chunksOf_spec (n : Nat) (hn : 0 < n) (bs : List U8) :
    (chunksOf n bs).flatten = bs ∧ (chunksOf n bs).length = (bs.length + n - 1) / n ∧
    ∀ i c, (chunksOf n bs)[i]? = some c →
      c ≠ [] ∧ c.length ≤ n ∧ (i + 1 < (chunksOf n bs).length → c.length = n) := by
  induction h : bs.length using Nat.strong_induction_on generalizing bs with
  | _ L ih =>
    by_cases hb : bs = []
    · subst hb
      simp only [List.length_nil] at h; subst h
      simp [chunksOf_nil]
      omega
    · have hL : 0 < L := by subst h; exact List.length_pos_iff.mpr hb
      obtain ⟨ih1, ih2, ih3⟩ := ih (bs.drop n).length (by simp; omega) (bs.drop n) rfl
      rw [chunksOf_cons n hn bs hb]
      refine ⟨by simp [ih1], ?_, ?_⟩
      · simp only [List.length_cons, ih2, List.length_drop, h]
        by_cases hle : L ≤ n
        · rw [Nat.sub_eq_zero_of_le hle]
          simp
          rw [Nat.div_eq_of_lt (by omega)]
          symm; rw [Nat.div_eq_iff (by omega)]; omega
        · have : L + n - 1 = (L - n + n - 1) + n := by omega
          rw [this, Nat.add_div_right _ hn]
      · intro i c hc
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          refine ⟨by simp [hb]; omega, by simp, ?_⟩
          intro hi
          simp only [List.length_cons] at hi
          have : chunksOf n (bs.drop n) ≠ [] := by
            intro e; rw [e] at hi; simp at hi
          have hd : bs.drop n ≠ [] := by intro e; rw [e, chunksOf_nil] at this; exact this rfl
          simp at hd ⊢; omega
        | succ i =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨a, b, c'⟩ := ih3 i c hc
          refine ⟨a, b, fun hi => c' (by simpa using hi)⟩

/-- At compression level 0 the compressed form is unique: every piece is stored. -/
theorem compEncoding_level_zero (d0 : flate2.mem.Compress) (n seq : Nat) (plain out : List U8) :
    CompEncoding d0 0 n seq plain out ↔
      out = compPackets seq (chunksOf n plain) ((chunksOf n plain).map fun _ => none) := by
  have key : ∀ (cs : List (List U8)) (zs : List (Option (List U8))),
      List.Forall₂ (EncChoice d0 0) cs zs ↔ zs = cs.map fun _ => none := by
    intro cs
    induction cs with
    | nil => intro zs; cases zs <;> simp
    | cons c cs ih =>
      intro zs
      cases zs with
      | nil => simp
      | cons z zs =>
        simp only [List.forall₂_cons, ih, List.map_cons, List.cons.injEq, and_congr_left_iff]
        intro _
        cases z with
        | none => simp [EncChoice, CompChoice]
        | some z => simp [EncChoice, CompChoice]
  constructor
  · rintro ⟨zs, h1, h2⟩
    rw [(key _ _).mp h1] at h2; exact h2
  · intro h
    exact ⟨_, (key _ _).mpr rfl, h⟩

/-- The crate's encoding is one of the streams the decoder accepts: its pieces are `chunksOf n plain`, each stored or deflated by flate2. Together with `chunksOf_spec` (pieces non-empty and at most `n` bytes) and `chunksOf_dropLast_length`, this gives `decode_compStream`'s hypotheses, so `PacketCodec.encode_decode_comp` follows from it. -/
theorem compEncoding_compStreamOf (d0 : flate2.mem.Compress) (level n seq : Nat) (plain out : List U8)
    (h : CompEncoding d0 level n seq plain out) : CompStreamOf seq (chunksOf n plain) out := by
  obtain ⟨zs, h1, h2⟩ := h
  refine ⟨zs, h1.imp ?_, h2⟩
  intro c zo hc z hz
  subst hz
  exact hc.1.2.2

/-- All pieces of `chunksOf n bs` but the last hold fewer bytes than `bs` (for `n > 0` and non-empty `bs`): the stream ends in the last piece (`decode_compStream`'s `hlast`, with `rest = []`). -/
theorem chunksOf_dropLast_length (n : Nat) (hn : 0 < n) (bs : List U8) (hbs : bs ≠ []) :
    (chunksOf n bs).dropLast.flatten.length < bs.length := by
  have ⟨h1, _, h3⟩ := chunksOf_spec n hn bs
  have hne : chunksOf n bs ≠ [] := by rw [chunksOf_cons n hn bs hbs]; simp
  have hl := List.dropLast_append_getLast hne
  have hlast := h3 ((chunksOf n bs).length - 1) ((chunksOf n bs).getLast hne)
    (by rw [List.getLast_eq_getElem, List.getElem?_eq_getElem])
  have : bs.length = (chunksOf n bs).dropLast.flatten.length + ((chunksOf n bs).getLast hne).length := by
    conv_lhs => rw [← h1, ← hl]
    simp
  have := hlast.1
  have : 0 < ((chunksOf n bs).getLast hne).length := List.length_pos_iff.mpr this
  omega

/-- `CompState.of` is injective: the state keeps the decoder's variant (stored vs compressed, even for a caller-built `Compressed(n, 0)`) and all its fields. -/
theorem CompState.of_injective (a b : proto.codec.CompDecoder) (h : CompState.of a = CompState.of b) : a = b := by
  rcases a with _ | ⟨s, (⟨n, p⟩ | ⟨n⟩)⟩ <;> rcases b with _ | ⟨s', (⟨n', p'⟩ | ⟨n'⟩)⟩ <;>
    simp_all [CompState.of]
  all_goals first
    | exact ⟨UScalar.eq_of_val_eq h.2.1, UScalar.eq_of_val_eq h.2.2⟩
    | exact UScalar.eq_of_val_eq h.2

/-- A stored packet is 7 bytes longer than its piece, and a deflated one is shorter than that (by `Trusted.deflateResult_short`, its payload is non-empty and shorter than the piece). -/
theorem compPacket_length (level seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hc : CompChoice level chunk zo) :
    (compPacket seq chunk zo).length ≤ 7 + chunk.length ∧
    (∀ z, zo = some z → 7 < (compPacket seq chunk zo).length ∧ (compPacket seq chunk zo).length < 7 + chunk.length) := by
  have hh : ∀ a b c, (compHeader a b c).length = 7 := by
    intro a b c; simp [compHeader, PBUtil.length_leBytes]
  cases zo with
  | none => simp [compPacket, hh]
  | some z =>
    obtain ⟨_, _, d, c, v, hc1, hv, hr⟩ := hc
    have := Trusted.deflateResult_short d c v hr
    subst hc1 hv
    simp only [compPacket, List.length_append, hh, Option.some.injEq, forall_eq']
    omega

/-- The reader reads back one packet written by the crate (stored, or deflated: by `Trusted.inflate_deflate`, with any inflate stream): the piece is appended, exactly the packet is consumed, idle again. -/
theorem compStep_compPacket (i : flate2.mem.Decompress) (seq : Nat) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (t dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    compStep (inflateList i) .idle (compPacket seq chunk zo ++ t) dst max =
      (.Ok (some (.Last (byte seq))), .idle, t, dst ++ chunk) := by
  have hM : maxPayloadLen = 2 ^ 24 - 1 := rfl
  have hm1 : chunk.length ≤ maxPayloadLen := le_trans hmax (Nat.min_le_left _ _)
  have hm2 : chunk.length ≤ max := le_trans hmax (Nat.min_le_right _ _)
  cases zo with
  | none =>
    obtain ⟨hl, hr⟩ := compHeaderRead_compHeader chunk.length seq 0 (by omega) (by norm_num) (chunk ++ t)
    simp only [compPacket, List.append_assoc]
    simp only [compStep, hr]
    have h7 : ¬ (compHeader chunk.length seq 0 ++ (chunk ++ t)).length < 7 := by simp [hl]
    have hmx : ¬ max < Nat.max chunk.length 0 := by simp; omega
    simp only [h7, hmx, ↓reduceIte]
    have hd7 : (compHeader chunk.length seq 0 ++ (chunk ++ t)).drop 7 = chunk ++ t := List.drop_left' hl
    by_cases h0 : chunk.length = 0
    · have : chunk = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      simp only [List.nil_append, List.length_nil] at hd7 ⊢
      simp [hd7]
    · have hle : 7 + chunk.length ≤ (compHeader chunk.length seq 0 ++ (chunk ++ t)).length := by simp [hl]
      simp only [h0, hle, ↓reduceIte, hd7]
      rw [← List.drop_drop, hd7]
      simp
  | some z =>
    have hd := hz z rfl
    obtain ⟨z0, zl⟩ := deflates_len chunk z hd
    obtain ⟨hl, hr⟩ := compHeaderRead_compHeader z.length seq chunk.length (by omega) (by omega) (z ++ t)
    simp only [compPacket, List.append_assoc]
    simp only [compStep, hr]
    have h7 : ¬ (compHeader z.length seq chunk.length ++ (z ++ t)).length < 7 := by simp [hl]
    have hmx : ¬ max < Nat.max z.length chunk.length := by simp; omega
    have hz0 : ¬ z.length = 0 := by omega
    have hc0 : ¬ chunk.length = 0 := by omega
    have hd7 : (compHeader z.length seq chunk.length ++ (z ++ t)).drop 7 = z ++ t := List.drop_left' hl
    have hle : 7 + z.length ≤ (compHeader z.length seq chunk.length ++ (z ++ t)).length := by simp [hl]
    simp only [h7, hmx, hz0, hc0, hle, ↓reduceIte, hd7, List.take_left' rfl, inflateList_deflates i chunk z hd]
    rw [← List.drop_drop, hd7]
    simp

/-- The reader keeps a valid state valid (for any inflate function). -/
theorem compStep_valid (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (st : CompState) (src dst : List U8) (max : Nat) (h : st.Valid) :
    (compStep inf st src dst max).2.1.Valid := by
  cases st with
  | idle =>
    obtain ⟨b1, b2⟩ := compHeaderRead_lt src
    rcases hh : compHeaderRead src with ⟨cl, sq, pl⟩
    rw [hh] at b1 b2
    simp only at b1 b2
    simp only [compStep, hh]
    split_ifs <;> try trivial
    all_goals (try split) <;> (try split) <;> simp_all [CompState.Valid]
    all_goals omega
  | packet seq cl pl =>
    simp only [compStep]
    split_ifs <;> try exact h
    split
    · trivial
    · split <;> trivial

private theorem compStep_prefix_hdr (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (cl seq pl : Nat) (X : List U8) (_hX : X.length = cl) (hcl0 : 0 < cl) (hcl : cl < 2 ^ 24)
    (hpl : pl < 2 ^ 24) (k : Nat) (hk : k < 7 + cl) (dst : List U8) (max : Nat)
    (hmax : Nat.max cl pl ≤ max) :
    (compStep inf .idle ((compHeader cl seq pl ++ X).take k) dst max).1 = .Ok none ∧
    (compStep inf .idle ((compHeader cl seq pl ++ X).take k) dst max).2.2 =
      ((compHeader cl seq pl ++ X).take k, dst) := by
  have hl := (compHeaderRead_compHeader cl seq pl hcl hpl []).1
  by_cases hk7 : k < 7
  · have : ((compHeader cl seq pl ++ X).take k).length < 7 := by simp; omega
    simp only [compStep, this, ↓reduceIte, and_self]
  · have ht : (compHeader cl seq pl ++ X).take k = compHeader cl seq pl ++ X.take (k - 7) := by
      rw [List.take_append, List.take_of_length_le (by omega), hl]
    have hr := (compHeaderRead_compHeader cl seq pl hcl hpl (X.take (k - 7))).2
    rw [ht]
    have h7 : ¬ (compHeader cl seq pl ++ X.take (k - 7)).length < 7 := by simp [hl]
    have hmx : ¬ max < Nat.max cl pl := by omega
    have hc0 : ¬ cl = 0 := by omega
    have hle : ¬ 7 + cl ≤ (compHeader cl seq pl ++ X.take (k - 7)).length := by simp [hl]; omega
    simp only [compStep, hr, h7, hmx, hc0, hle, ↓reduceIte, and_self]

/-- On a strict prefix of a packet, the reader asks for more input and consumes nothing. -/
theorem compStep_prefix (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hz : ∀ z, zo = some z → Deflates chunk z)
    (k : Nat) (hk : k < (compPacket seq chunk zo).length) (dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).1 = .Ok none ∧
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).2.2 =
      ((compPacket seq chunk zo).take k, dst) := by
  have hM : maxPayloadLen = 2 ^ 24 - 1 := rfl
  have hm1 : chunk.length ≤ maxPayloadLen := le_trans hmax (Nat.min_le_left _ _)
  have hm2 : chunk.length ≤ max := le_trans hmax (Nat.min_le_right _ _)
  cases zo with
  | none =>
    have hl := (compHeaderRead_compHeader chunk.length seq 0 (by omega) (by norm_num) []).1
    simp only [compPacket, List.length_append, hl] at hk ⊢
    by_cases h0 : chunk.length = 0
    · have : k < 7 := by omega
      have : ((compHeader chunk.length seq 0 ++ chunk).take k).length < 7 := by simp; omega
      simp only [compStep, this, ↓reduceIte, and_self]
    · exact compStep_prefix_hdr inf chunk.length seq 0 chunk rfl (by omega) (by omega) (by norm_num) k (by omega)
        dst max (by simp; omega)
  | some z =>
    obtain ⟨z0, zl⟩ := deflates_len chunk z (hz z rfl)
    have hl := (compHeaderRead_compHeader z.length seq chunk.length (by omega) (by omega) []).1
    simp only [compPacket, List.length_append, hl] at hk ⊢
    exact compStep_prefix_hdr inf z.length seq chunk.length z rfl z0 (by omega) (by omega) k (by omega)
      dst max (by simp; omega)

/-- `splitVersion` reads back `a.b.c` followed by anything that does not start with a digit, for parts in `0..=255` written in decimal. -/
theorem splitVersion_decimal (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (junk : List U8)
    (hj : ∀ d, junk.head? = some d → isDigit d = false) :
    splitVersion (decimalBytes a ++ byte 46 :: decimalBytes b ++ byte 46 :: decimalBytes c ++ junk) =
      some (byte a, byte b, byte c) := by
  have nd : ∀ n : Nat, ∀ x ∈ decimalBytes (n : Int), (fun c : U8 => decide (c.val ≠ 46)) x = true := by
    intro n x hx; have := decimal_digit n x hx; simp; omega
  have dig : ∀ n : Nat, ∀ x ∈ decimalBytes (n : Int), isDigit x = true := by
    intro n x hx; have := decimal_digit n x hx; simp [isDigit]; omega
  have h46 : (byte 46).val = 46 := rfl
  unfold splitVersion
  simp only [List.append_assoc, List.cons_append]
  have e1 := dropWhile_append_all (fun c : U8 => decide (c.val ≠ 46)) _
    (byte 46 :: (decimalBytes b ++ (byte 46 :: (decimalBytes c ++ junk)))) (nd a)
  have e2 := dropWhile_append_all (fun c : U8 => decide (c.val ≠ 46)) _
    (byte 46 :: (decimalBytes c ++ junk)) (nd b)
  have e3 := takeWhile_append_all (fun c : U8 => decide (c.val ≠ 46)) _
    (byte 46 :: (decimalBytes b ++ (byte 46 :: (decimalBytes c ++ junk)))) (nd a)
  have e4 := takeWhile_append_all (fun c : U8 => decide (c.val ≠ 46)) _
    (byte 46 :: (decimalBytes c ++ junk)) (nd b)
  have e5 := takeWhile_append_all isDigit _ junk (dig c)
  have hjt : junk.takeWhile isDigit = [] := by
    cases junk with
    | nil => rfl
    | cons d r => simp [hj d rfl]
  rw [List.dropWhile_cons_of_neg (p := fun c : U8 => decide (c.val ≠ 46)) (by simp [h46])] at e1 e2
  rw [List.takeWhile_cons_of_neg (p := fun c : U8 => decide (c.val ≠ 46)) (by simp [h46])] at e3 e4
  simp only [e1, e2, e3, e4, e5, hjt]
  simp [versionPart_decimal a ha, versionPart_decimal b hb, versionPart_decimal c hc]

/-- The crate's test cases: `"1.2.3"`, `"10.20.30foo"`, `"100.200.300foo"` (a part above 255: none), and two quirks: a sign is accepted in the first two parts, and fewer than two dots give none. -/
theorem splitVersion_examples :
    splitVersion (utf8 "1.2.3") = some (byte 1, byte 2, byte 3) ∧
    splitVersion (utf8 "10.20.30foo") = some (byte 10, byte 20, byte 30) ∧
    splitVersion (utf8 "8.0.36-log") = some (byte 8, byte 0, byte 36) ∧
    splitVersion (utf8 "100.200.300foo") = none ∧
    splitVersion (utf8 "+5.-0.7") = some (byte 5, byte 0, byte 7) ∧
    splitVersion (utf8 "8.0") = none ∧
    splitVersion (utf8 "8.0.x") = none := by
  decide

end Defs
