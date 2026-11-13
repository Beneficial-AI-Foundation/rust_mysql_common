import Defs
import Proofs.Util.CompCodec

/-! Statements for `fn split_version` and `fn split_version_inner` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- The first index `r` at or after `start` where `p` fails (or the length). -/
private def StopAt (p : U8 → Bool) (l : List U8) (start r : Nat) : Prop :=
  start ≤ r ∧ r ≤ l.length ∧ (∀ j (hj : j < l.length), start ≤ j → j < r → p l[j] = true) ∧
    (∀ h : r < l.length, p l[r] = false)

private theorem dot_body (input : Slice U8) (start i : Usize)
    (hinv : start.val ≤ i.val ∧ i.val ≤ input.val.length ∧
      ∀ j (hj : j < input.val.length), start.val ≤ j → j < i.val → (fun c : U8 => decide (c.val ≠ 46)) input.val[j] = true) :
    misc.dot_or_end_loop.body input i ⦃ r =>
      match r with
      | .done y => StopAt (fun c : U8 => decide (c.val ≠ 46)) input.val start.val y.val
      | .cont x' => (start.val ≤ x'.val ∧ x'.val ≤ input.val.length ∧
          ∀ j (hj : j < input.val.length), start.val ≤ j → j < x'.val → (fun c : U8 => decide (c.val ≠ 46)) input.val[j] = true) ∧
          input.val.length - x'.val < input.val.length - i.val ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hinv
  unfold misc.dot_or_end_loop.body
  step*
  · have hl : i.val < input.val.length := by scalar_tac
    refine ⟨h1, by omega, fun j hj hs hl' => h3 j hj hs hl', fun h => ?_⟩
    have e : input.val[i.val] = 46#u8 := by rwa [← i2_post]
    simp [e]
  · have hl : i.val < input.val.length := by scalar_tac
    refine ⟨by omega, by omega, fun j hj hs hl' => ?_, by omega⟩
    by_cases hji : j < i.val
    · exact h3 j hj hs hji
    · have : j = i.val := by omega
      subst this
      have hne : ¬ i2.val = 46 := fun e => by apply ‹¬i2 = 46#u8›; apply UScalar.eq_of_val_eq; simpa using e
      simp only [← i2_post]; simpa using hne
  · have hl : input.val.length ≤ i.val := by scalar_tac
    have e : input.len.val = input.val.length := by simp
    refine ⟨by omega, by omega, fun j hj hs hl' => h3 j hj hs (by omega), fun h => by omega⟩

private theorem dot_loop (input : Slice U8) (start : Usize) (hs : start.val ≤ input.val.length) :
    misc.dot_or_end_loop input start ⦃ r => StopAt (fun c : U8 => decide (c.val ≠ 46)) input.val start.val r.val ⦄ := by
  unfold misc.dot_or_end_loop
  apply loop.spec_decr_nat (fun i => input.val.length - i.val) (fun i => start.val ≤ i.val ∧ i.val ≤ input.val.length ∧
      ∀ j (hj : j < input.val.length), start.val ≤ j → j < i.val → (fun c : U8 => decide (c.val ≠ 46)) input.val[j] = true)
  · intro i hi
    apply spec_mono (dot_body input start i hi)
    intro r h; cases r <;> exact h
  · exact ⟨le_refl _, hs, fun j _ h1 h2 => by omega⟩

private theorem dig_body (input : Slice U8) (i : Usize)
    (hinv : i.val ≤ input.val.length ∧
      ∀ j (hj : j < input.val.length), j < i.val → isDigit input.val[j] = true) :
    misc.digits_end_loop.body input i ⦃ r =>
      match r with
      | .done y => StopAt isDigit input.val 0 y.val
      | .cont x' => (x'.val ≤ input.val.length ∧
          ∀ j (hj : j < input.val.length), j < x'.val → isDigit input.val[j] = true) ∧
          input.val.length - x'.val < input.val.length - i.val ⦄ := by
  obtain ⟨h2, h3⟩ := hinv
  unfold misc.digits_end_loop.body
  step*
  · have hl : i.val < input.val.length := by scalar_tac
    refine ⟨by omega, by omega, fun j hj _ hl' => h3 j hj hl', fun h => ?_⟩
    have : i2.val < 48 := by scalar_tac
    simp only [← i2_post, isDigit]; simp; omega
  · have hl : i.val < input.val.length := by scalar_tac
    refine ⟨by omega, by omega, fun j hj _ hl' => h3 j hj hl', fun h => ?_⟩
    have : 57 < i2.val := by scalar_tac
    simp only [← i2_post, isDigit]; simp; omega
  · have hl : i.val < input.val.length := by scalar_tac
    refine ⟨by omega, fun j hj hl' => ?_, by omega⟩
    by_cases hji : j < i.val
    · exact h3 j hj hji
    · have : j = i.val := by omega
      subst this
      have : 48 ≤ i2.val := by scalar_tac
      have : i2.val ≤ 57 := by scalar_tac
      simp only [← i2_post, isDigit]; simp; omega
  · have hl : input.val.length ≤ i.val := by scalar_tac
    have e : input.len.val = input.val.length := by simp
    refine ⟨by omega, by omega, fun j hj _ hl' => h3 j hj (by omega), fun h => by omega⟩

@[step]
private theorem dig_loop (input : Slice U8) :
    misc.digits_end_loop input 0#usize ⦃ r => StopAt isDigit input.val 0 r.val ⦄ := by
  unfold misc.digits_end_loop
  apply loop.spec_decr_nat (fun i => input.val.length - i.val) (fun i => i.val ≤ input.val.length ∧
      ∀ j (hj : j < input.val.length), j < i.val → isDigit input.val[j] = true)
  · intro i hi
    apply spec_mono (dig_body input i hi)
    intro r h; cases r <;> exact h
  · exact ⟨by simp, fun j _ h => by simp at h⟩

private theorem StopAt.while (p : U8 → Bool) (l : List U8) (n : Nat) (h : StopAt p l 0 n) :
    l.takeWhile p = l.take n ∧ l.dropWhile p = l.drop n := by
  obtain ⟨_, hn, hall, hstop⟩ := h
  induction l generalizing n with
  | nil => simp
  | cons x l ih =>
    cases n with
    | zero =>
      have := hstop (by simp)
      simp only [List.getElem_cons_zero] at this
      simp [this]
    | succ n =>
      have hx : p x = true := hall 0 (by simp) (le_refl _) (by omega)
      obtain ⟨a, b⟩ := ih n (by omega) (by simp at hn; omega)
        (fun j hj _ hjn => by
          have := hall (j + 1) (by simp; omega) (by omega) (by omega)
          rwa [List.getElem_cons_succ] at this)
        (fun h => by
          have := hstop (by simp; omega)
          rwa [List.getElem_cons_succ] at this)
      simp [hx, a, b]

private theorem StopAt.drop (p : U8 → Bool) (l : List U8) (st r : Nat) (h : StopAt p l st r) :
    StopAt p (l.drop st) 0 (r - st) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨Nat.zero_le _, by simp; omega, fun j hj _ hjr => ?_, fun h => ?_⟩
  · simp only [List.getElem_drop]; exact h2 _ (by simp at hj; omega) (by omega) (by omega)
  · simp only [List.getElem_drop]
    have := h3 (by simp at h; omega)
    simp only [show st + (r - st) = r by omega]; exact this

private theorem takeWhile_take_stop (p : U8 → Bool) (l : List U8) (m : Nat) (h : ∀ hm : m < l.length, p l[m] = false) :
    l.takeWhile p = (l.take m).takeWhile p := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    cases m with
    | zero => simp at h; simp [h]
    | succ m =>
      simp only [List.take_succ_cons, List.takeWhile_cons]
      rw [ih m (fun hm => by
        have := h (by simp; omega)
        rwa [List.getElem_cons_succ] at this)]

private theorem take_of_stopAt (p : U8 → Bool) (l : List U8) (n : Nat) (h : StopAt p l 0 n) :
    l.take n = l.takeWhile p := (StopAt.while p l n h).1.symm

private theorem btoi_u8_eq (s : Slice U8) : Trusted.btoiUnsigned .U8 s = versionPart s.val := by
  simp only [Trusted.btoiUnsigned, versionPart, ConvInts.btoiValue_eq_asciiInt]
  cases asciiInt s.val with
  | none => rfl
  | some v =>
    simp only [Option.bind_some]
    by_cases h0 : 0 ≤ v
    · have := UScalar.tryMkOpt_eq .U8 v.toNat
      by_cases h1 : v < 256
      · simp only [h0, h1, and_self, ↓reduceIte]
        split at this
        · rename_i y hy
          rw [hy]; congr 1; apply UScalar.eq_of_val_eq
          rw [this.1, PBUtil.byte_val]; omega
        · exfalso; apply this; simp [UScalar.inBounds]; omega
      · simp only [h0, h1, and_false, ↓reduceIte]
        split at this
        · exfalso; have := this.2; simp [UScalar.inBounds] at this; omega
        · assumption
    · simp [h0]

private theorem inner_eq' (input : Slice U8) :
    misc.split_version_inner input = ok (splitVersion input.val) := by
  suffices h : misc.split_version_inner input ⦃ r => r = splitVersion input.val ⦄ by
    obtain ⟨v, hv, rfl⟩ := PBUtil.spec_eq_ok h; exact hv
  unfold misc.split_version_inner misc.dot_or_end
  step with dot_loop input 0#usize (by simp) as ⟨end0, h0⟩
  obtain ⟨tw0, dw0⟩ := StopAt.while _ _ _ h0
  have hsv : splitVersion input.val = (match input.val.drop end0.val with
      | [] => none
      | _ :: r0 =>
        match r0.dropWhile (fun c : U8 => decide (c.val ≠ 46)) with
        | [] => none
        | _ :: r1 => do
          let a ← versionPart (input.val.take end0.val)
          let b ← versionPart (r0.takeWhile (fun c : U8 => decide (c.val ≠ 46)))
          let c ← versionPart (r1.takeWhile isDigit)
          some (a, b, c)) := by
    unfold splitVersion; simp only [dw0, tw0]; rfl
  rw [hsv]
  obtain ⟨-, hle0, -, hst0⟩ := h0
  have elen : input.len.val = input.val.length := by simp
  by_cases he0 : end0 = input.len
  · have : end0.val = input.val.length := by rw [he0, elen]
    simp [he0]
  · have hlt0 : end0.val < input.val.length := by
      have : end0.val ≠ input.len.val := fun e => he0 (UScalar.eq_of_val_eq e)
      omega
    simp only [he0, ↓reduceIte]
    rw [List.drop_eq_getElem_cons hlt0]
    simp only
    step*
    rw [← i1_post]
    step with dot_loop input i1 (by omega) as ⟨end1, h1⟩
    obtain ⟨tw1, dw1⟩ := StopAt.while _ _ _ (StopAt.drop _ _ _ _ h1)
    obtain ⟨hge1, hle1, -, hst1⟩ := h1
    rw [tw1, dw1, List.drop_drop, show i1.val + (end1.val - i1.val) = end1.val by omega]
    by_cases he1 : end1 = input.len
    · have : end1.val = input.val.length := by rw [he1, elen]
      simp [he1]
    · have hlt1 : end1.val < input.val.length := by
        have : end1.val ≠ input.len.val := fun e => he1 (UScalar.eq_of_val_eq e)
        omega
      simp only [he1, ↓reduceIte]
      rw [List.drop_eq_getElem_cons hlt1]
      simp only
      step*
      rw [← i3_post]
      step with dot_loop input i3 (by omega) as ⟨end2, h2⟩
      obtain ⟨hge2, hle2, -, hst2⟩ := h2
      have hp1 : List.takeWhile isDigit (List.drop i3.val input.val) =
          List.takeWhile isDigit (List.slice i3.val end2.val input.val) := by
        rw [List.slice]
        apply takeWhile_take_stop
        intro hm
        have := hst2 (by simp only [List.length_drop] at hm; omega)
        simp only [List.getElem_drop, show i3.val + (end2.val - i3.val) = end2.val by omega]
        simp only [decide_eq_false_iff_not, not_not] at this
        simp [isDigit, this]
      rw [hp1]
      simp only [value.convert.trusted.btoi_u8, btoi_u8_eq, misc.digits_end]
      step*
      · simp_all [List.slice]
      · simp_all [List.slice]
      · rw [List.slice_zero_j, take_of_stopAt _ _ _ i4_post] at chunk_post
        simp_all [List.slice]
      · rw [List.slice_zero_j, take_of_stopAt _ _ _ i4_post] at chunk_post
        simp_all [List.slice]


/-- `split_version(version_str)`: total, exact on any input. It returns `splitVersion` (the crate's reading; no protocol defines it) of the string's bytes: the major and minor parts (before the first and second `.`), and the run of ASCII digits starting the third part, each a number in `0..=255`. It returns `(0, 0, 0)` if there are fewer than two `.` or a part is not such a number. **Quirks:**
    * a failure is indistinguishable from version `0.0.0`;
    * the first two parts may carry a sign (`"+5.-0.7"` gives `(5, 0, 7)`: a btoi quirk);
    * a part above 255 makes the whole result `(0, 0, 0)`.
    Stated for any `AsRef<[u8]>` whose `as_ref` returns. -/
theorem misc.split_version_eq {T : Type} (inst : core.convert.AsRef T (Slice U8)) (x : T) (s : Slice U8)
    (hs : inst.as_ref x = ok s) :
    misc.split_version inst x = ok ((splitVersion s.val).getD (0#u8, 0#u8, 0#u8)) := by
  simp [misc.split_version, hs, inner_eq']
  cases splitVersion s.val <;> rfl

/-- `split_version_inner(input)`: total; exactly `splitVersion`. -/
theorem misc.split_version_inner_eq (input : Slice U8) :
    misc.split_version_inner input = ok (splitVersion input.val) := by
  exact inner_eq' input

end mysql_common
