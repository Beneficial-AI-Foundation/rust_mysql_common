import Defs
import Proofs.Util.ConvBytesTime
import Proofs.Util.ConvNonAscii

/-! Statements for `fn parse_mysql_time_string` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil mysql_common.NAUtil

namespace mysql_common

/-! ### The text `TIME` literal after its sign -/

/-- `timeStringRead` after the optional sign (`neg`): the hours and the rest. -/
private def tsrRest (neg : Bool) (t : List U8) : Option (Bool × Nat × Nat × Nat × Nat) :=
  let hours : Option (Nat × List U8) :=
    match t with
    | h1 :: h2 :: h3 :: rest =>
      if digitUpTo 8 h1 ∧ isDigit h2 ∧ isDigit h3 then some (digitsVal [h1, h2, h3], rest)
      else if isDigit h1 ∧ isDigit h2 then some (digitsVal [h1, h2], h3 :: rest)
      else none
    | _ => none
  match hours with
  | some (h, c1 :: m1 :: m2 :: c2 :: s1 :: s2 :: frac) =>
    if c1.val = 58 ∧ c2.val = 58 ∧ digitUpTo 5 m1 ∧ isDigit m2 ∧ digitUpTo 5 s1 ∧ isDigit s2 then
      (fracRead frac).map fun us => (neg, h, digitsVal [m1, m2], digitsVal [s1, s2], us)
    else none
  | _ => none

private theorem timeStringRead_cons (c : U8) (rest : List U8) :
    timeStringRead (c :: rest) =
      if c.val = 45 then tsrRest true rest else tsrRest false (c :: rest) := by
  by_cases hc : c.val = 45
  · simp only [timeStringRead, hc, ite_true]; rfl
  · simp only [timeStringRead, hc, ite_false]; rfl

private theorem tsrRest_len (neg : Bool) (t : List U8) (h : tsrRest neg t ≠ none) : 8 ≤ t.length := by
  unfold tsrRest at h
  match t with
  | [] | [_] | [_, _] => simp at h
  | h1 :: h2 :: h3 :: rest =>
    simp only at h
    split at h
    · rename_i hh
      split at hh
      · rename_i e; cases e; simp_all
      · split at hh
        · rename_i e; cases e; simp_all
        · cases hh
    · simp at h

private theorem lt128_isDigit (b : U8) (h : Trusted.isAsciiDigit b = true) : isDigit b = true := h

private theorem digit_eq : Trusted.digit = isDigit := rfl

/-- `HH:MM:SS` (`TIME_RE_HH_MM_SS`, on ASCII input). -/
private theorem tsr_hh (neg : Bool) (t : List U8) (hR : Trusted.Regex.asciiMatch .timeHhMmSs t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U8, t = [a0, a1, a2, a3, a4, a5, a6, a7] ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a3 ∧ isDigit a4 ∧ isDigit a6 ∧ isDigit a7) ∧
      tsrRest neg t = some (neg, digitsVal [a0, a1], digitsVal [a3, a4], digitsVal [a6, a7], 0) := by
  match t with
  | [a0, a1, a2, a3, a4, a5, a6, a7] =>
    simp only [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, List.cons_append,
      List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Trusted.byteIn,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl, ?_, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]; omega
    · simp_all [tsrRest, isAsciiDigit_eq, isDigit, digitUpTo, fracRead]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, Trusted.matchSeq] at hR
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, Trusted.matchSeq] at hR

/-- `HHH:MM:SS` (`TIME_RE_HHH_MM_SS`, on ASCII input). -/
private theorem tsr_hhh (neg : Bool) (t : List U8) (hR : Trusted.Regex.asciiMatch .timeHhhMmSs t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 : U8, t = [a0, a1, a2, a3, a4, a5, a6, a7, a8] ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a4 ∧ isDigit a5 ∧ isDigit a7 ∧ isDigit a8) ∧
      tsrRest neg t = some (neg, digitsVal [a0, a1, a2], digitsVal [a4, a5], digitsVal [a7, a8], 0) := by
  match t with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8] =>
    simp only [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, List.cons_append,
      List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Trusted.byteIn,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rfl, ?_, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]; omega
    · simp_all [tsrRest, isDigit, digitUpTo, fracRead, Trusted.isAsciiDigit]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, Trusted.matchSeq] at hR
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, Trusted.matchSeq] at hR

private theorem matchFrac_iff (l : List U8) (h : Trusted.matchFrac l = true) :
    ∃ c ds, l = c :: ds ∧ c.val = 46 ∧ ds ≠ [] ∧ ds.all isDigit ∧ ds.length ≤ 6 := by
  match l with
  | [] => simp [Trusted.matchFrac] at h
  | c :: ds =>
    simp only [Trusted.matchFrac, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨c, ds, rfl, h.1.1.1, ?_, ?_, h.1.2⟩
    · intro e; subst e; simp at h
    · simpa [isAsciiDigit_eq] using h.2

private theorem fracRead_dot (c : U8) (ds : List U8) (hc : c.val = 46) (h1 : ds ≠ [])
    (h2 : ds.all isDigit) (h3 : ds.length ≤ 6) : fracRead (c :: ds) = some (fracVal ds) := by
  have : 1 ≤ ds.length := by cases ds <;> simp_all
  simp [fracRead, hc, h2, h3, this, fracVal]

/-- `HH:MM:SS.f` (`TIME_RE_HH_MM_SS_MS`, on ASCII input). -/
private theorem tsr_hh_ms (neg : Bool) (t : List U8)
    (hR : Trusted.Regex.asciiMatch .timeHhMmSsMs t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 : U8, ∃ ds : List U8,
      t = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: ds ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a3 ∧ isDigit a4 ∧ isDigit a6 ∧ isDigit a7) ∧
      (ds ≠ [] ∧ ds.all isDigit ∧ ds.length ≤ 6) ∧
      tsrRest neg t = some (neg, digitsVal [a0, a1], digitsVal [a3, a4], digitsVal [a6, a7], fracVal ds) := by
  match t with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    simp only [Trusted.Regex.asciiMatch, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, Bool.and_eq_true] at hR
    obtain ⟨hR, hF⟩ := hR
    obtain ⟨a8, ds, rfl, h8, hd1, hd2, hd3⟩ := matchFrac_iff rest hF
    simp only [Trusted.hhmmss, Trusted.mmss, List.cons_append,
      List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Trusted.byteIn,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, ds, rfl, ?_, ⟨hd1, hd2, hd3⟩, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]; omega
    · have hf := fracRead_dot a8 ds h8 hd1 hd2 hd3
      simp only [tsrRest]
      simp_all [isDigit, digitUpTo, Trusted.isAsciiDigit]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, Trusted.matchSeq] at hR

/-- `HHH:MM:SS.f` (`TIME_RE_HHH_MM_SS_MS`, on ASCII input). -/
private theorem tsr_hhh_ms (neg : Bool) (t : List U8)
    (hR : Trusted.Regex.asciiMatch .timeHhhMmSsMs t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U8, ∃ ds : List U8,
      t = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: ds ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a4 ∧ isDigit a5 ∧ isDigit a7 ∧ isDigit a8) ∧
      (ds ≠ [] ∧ ds.all isDigit ∧ ds.length ≤ 6) ∧
      tsrRest neg t = some (neg, digitsVal [a0, a1, a2], digitsVal [a4, a5], digitsVal [a7, a8], fracVal ds) := by
  match t with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest =>
    simp only [Trusted.Regex.asciiMatch, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, Bool.and_eq_true] at hR
    obtain ⟨hR, hF⟩ := hR
    obtain ⟨a9, ds, rfl, h9, hd1, hd2, hd3⟩ := matchFrac_iff rest hF
    simp only [Trusted.hhhmmss, Trusted.mmss, List.cons_append,
      List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Trusted.byteIn,
      Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, ds, rfl, ?_, ⟨hd1, hd2, hd3⟩, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]; omega
    · have hf := fracRead_dot a9 ds h9 hd1 hd2 hd3
      simp only [tsrRest]
      simp_all [isDigit, digitUpTo, Trusted.isAsciiDigit]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] =>
    simp [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, Trusted.matchSeq] at hR

/-- A text `TIME` literal (after the sign) matches one of the four regexes. -/
private theorem tsr_some (neg : Bool) (t : List U8) (h : tsrRest neg t ≠ none) :
    (t.length = 8 ∧ Trusted.Regex.asciiMatch .timeHhMmSs t = true) ∨
    (t.length = 9 ∧ Trusted.Regex.asciiMatch .timeHhhMmSs t = true) ∨
    Trusted.Regex.asciiMatch .timeHhMmSsMs t = true ∨
    Trusted.Regex.asciiMatch .timeHhhMmSsMs t = true := by
  unfold tsrRest at h
  match t with
  | [] | [_] | [_, _] => simp at h
  | h1 :: h2 :: h3 :: rest =>
    simp only at h
    by_cases c3 : digitUpTo 8 h1 ∧ isDigit h2 ∧ isDigit h3
    · simp only [c3, and_self, ite_true] at h
      match rest with
      | c1 :: m1 :: m2 :: c2 :: s1 :: s2 :: frac =>
        simp only at h
        split_ifs at h with hc
        · simp only [digitUpTo, isDigit, Bool.and_eq_true, decide_eq_true_eq] at c3 hc
          cases frac with
          | nil =>
            right; left
            simp [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, Trusted.matchSeq,
              Trusted.digit, Trusted.isAsciiDigit, Trusted.byteIn, Trusted.lit]
            omega
          | cons f ds =>
            right; right; right
            simp only [fracRead] at h
            split_ifs at h with hf
            · simp [Trusted.Regex.asciiMatch, Trusted.hhhmmss, Trusted.mmss, Trusted.matchSeq,
                Trusted.digit, Trusted.isAsciiDigit, Trusted.byteIn, Trusted.lit, Trusted.matchFrac]
              have hd : ∀ x ∈ ds, 48 ≤ x.val ∧ x.val ≤ 57 := by simpa [isDigit] using hf.2.2.2
              and_intros
              all_goals omega
            · simp at h
        · simp at h
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => simp at h
    · simp only [c3, ite_false] at h
      by_cases c2 : isDigit h1 ∧ isDigit h2
      · simp only [c2, and_self, ite_true] at h
        match rest with
        | m1 :: m2 :: c2' :: s1 :: s2 :: frac =>
          simp only at h
          split_ifs at h with hc
          · simp only [digitUpTo, isDigit, Bool.and_eq_true, decide_eq_true_eq] at c2 hc
            cases frac with
            | nil =>
              left
              simp [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, Trusted.matchSeq,
                Trusted.digit, Trusted.isAsciiDigit, Trusted.byteIn, Trusted.lit]
              omega
            | cons f ds =>
              right; right; left
              simp only [fracRead] at h
              split_ifs at h with hf
              · simp [Trusted.Regex.asciiMatch, Trusted.hhmmss, Trusted.mmss, Trusted.matchSeq,
                  Trusted.digit, Trusted.isAsciiDigit, Trusted.byteIn, Trusted.lit, Trusted.matchFrac]
                have hd : ∀ x ∈ ds, 48 ≤ x.val ∧ x.val ≤ 57 := by simpa [isDigit] using hf.2.2.2
                and_intros
                all_goals omega
              · simp at h
          · simp at h
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp at h
      · simp [c2] at h

/-- The `HH:MM:SS[.f]` block: reads the fields at their positions. -/
private theorem hh_block_spec (b : Slice U8) (neg : Bool) (M : Option (core.ops.range.RangeFrom Usize))
    (a0 a1 a2 a3 a4 a5 a6 a7 : U8) (rest : List U8)
    (hb : b.val = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest)
    (hd : isDigit a0 ∧ isDigit a1 ∧ isDigit a3 ∧ isDigit a4 ∧ isDigit a6 ∧ isDigit a7)
    (hM : ∀ st : core.ops.range.RangeFrom Usize, M = some st → st.start.val ≤ b.length ∧
      b.val.drop st.start.val ≠ [] ∧ (b.val.drop st.start.val).all isDigit ∧
      (b.val.drop st.start.val).length ≤ 6) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            M b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r =>
      ∃ h m sec us, r = some (neg, h, m, sec, us) ∧ h.val = digitsVal [a0, a1] ∧
        m.val = digitsVal [a3, a4] ∧ sec.val = digitsVal [a6, a7] ∧
        us.val = (M.map fun st => fracVal (b.val.drop st.start.val)).getD 0 ⦄ := by
  obtain ⟨d0, d1, d3, d4, d6, d7⟩ := hd
  step*
  all_goals try simp_all [List.slice, Slice.length]
  all_goals (rcases M with _ | _ <;> rcases o3 with _ | _ <;> simp_all [core.option.Option.unwrap_or])


/-- The `HHH:MM:SS[.f]` block: reads the fields at their positions. -/
private theorem hhh_block_spec (b : Slice U8) (neg : Bool) (M : Option (core.ops.range.RangeFrom Usize))
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : U8) (rest : List U8)
    (hb : b.val = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest)
    (hd : isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a4 ∧ isDigit a5 ∧ isDigit a7 ∧ isDigit a8)
    (hM : ∀ st : core.ops.range.RangeFrom Usize, M = some st → st.start.val ≤ b.length ∧
      b.val.drop st.start.val ≠ [] ∧ (b.val.drop st.start.val).all isDigit ∧
      (b.val.drop st.start.val).length ≤ 6) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 3#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 4#usize, «end» := 6#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 7#usize, «end» := 9#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            M b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r =>
      ∃ h m sec us, r = some (neg, h, m, sec, us) ∧ h.val = digitsVal [a0, a1, a2] ∧
        m.val = digitsVal [a4, a5] ∧ sec.val = digitsVal [a7, a8] ∧
        us.val = (M.map fun st => fracVal (b.val.drop st.start.val)).getD 0 ⦄ := by
  obtain ⟨d0, d1, d2, d4, d5, d7, d8⟩ := hd
  step*
  all_goals try simp_all [List.slice, Slice.length]
  all_goals (rcases M with _ | _ <;> rcases o3 with _ | _ <;> simp_all [core.option.Option.unwrap_or])

/-- What the parser returns, as `(negative, hours, minutes, seconds, microseconds)`. -/
private def tview (t : Bool × U32 × U8 × U8 × U32) : Bool × Nat × Nat × Nat × Nat :=
  (t.1, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.val)

private theorem leaf_hh (b : Slice U8) (neg : Bool)
    (hR : Trusted.Regex.asciiMatch .timeHhMmSs b.val = true) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            none b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r => r.map tview = tsrRest neg b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ht, hd, hv⟩ := tsr_hh neg _ hR
  apply WP.spec_mono (hh_block_spec b neg none a0 a1 a2 a3 a4 a5 a6 a7 [] (by simp [ht]) hd (by simp))
  rintro r ⟨h, m, sec, us, rfl, e1, e2, e3, e4⟩
  rw [hv]; simp [tview, e1, e2, e3, e4]

private theorem leaf_hhh (b : Slice U8) (neg : Bool)
    (hR : Trusted.Regex.asciiMatch .timeHhhMmSs b.val = true) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 3#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 4#usize, «end» := 6#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 7#usize, «end» := 9#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            none b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r => r.map tview = tsrRest neg b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, ht, hd, hv⟩ := tsr_hhh neg _ hR
  apply WP.spec_mono (hhh_block_spec b neg none a0 a1 a2 a3 a4 a5 a6 a7 a8 [] (by simp [ht]) hd (by simp))
  rintro r ⟨h, m, sec, us, rfl, e1, e2, e3, e4⟩
  rw [hv]; simp [tview, e1, e2, e3, e4]

private theorem leaf_hh_ms (b : Slice U8) (neg : Bool)
    (hR : Trusted.Regex.asciiMatch .timeHhMmSsMs b.val = true) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            (some { start := 9#usize }) b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r => r.map tview = tsrRest neg b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, ds, ht, hd, ⟨h1, h2, h3⟩, hv⟩ := tsr_hh_ms neg _ hR
  apply WP.spec_mono (hh_block_spec b neg (some { start := 9#usize }) a0 a1 a2 a3 a4 a5 a6 a7 (a8 :: ds)
    (by simp [ht]) hd ?_)
  · rintro r ⟨h, m, sec, us, rfl, e1, e2, e3, e4⟩
    rw [hv]; simp [tview, e1, e2, e3, e4, ht]
  · rintro st ⟨⟩
    have : 1 ≤ ds.length := by cases ds <;> simp_all
    simp [ht, Slice.length, h1, h2, h3]

private theorem leaf_hhh_ms (b : Slice U8) (neg : Bool)
    (hR : Trusted.Regex.asciiMatch .timeHhhMmSsMs b.val = true) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 3#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 4#usize, «end» := 6#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 7#usize, «end» := 9#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            (some { start := 10#usize }) b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) ⦃ r => r.map tview = tsrRest neg b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, ds, ht, hd, ⟨h1, h2, h3⟩, hv⟩ := tsr_hhh_ms neg _ hR
  apply WP.spec_mono (hhh_block_spec b neg (some { start := 10#usize }) a0 a1 a2 a3 a4 a5 a6 a7 a8 (a9 :: ds)
    (by simp [ht]) hd ?_)
  · rintro r ⟨h, m, sec, us, rfl, e1, e2, e3, e4⟩
    rw [hv]; simp [tview, e1, e2, e3, e4, ht]
  · rintro st ⟨⟩
    have : 1 ≤ ds.length := by cases ds <;> simp_all
    simp [ht, Slice.length, h1, h2, h3]

/-- After the sign: dispatches on the length and the four regexes. -/
private theorem core_spec (bs1 : Slice U8) (neg : Bool) (ha : ∀ c ∈ bs1.val, c.val < 128) :
    (do
    let len := Slice.len bs1
    if len = 8#usize
    then
      let b ← value.convert.trusted.time_re_hh_mm_ss bs1
      if b
      then
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            none bs1
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))
      else
        if len = 9#usize
        then
          let b1 ← value.convert.trusted.time_re_hhh_mm_ss bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 3#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 4#usize, «end» := 6#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 7#usize, «end» := 9#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                none bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 2#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 3#usize, «end» := 5#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 6#usize, «end» := 8#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 9#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else
              let b3 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
              if b3
              then
                let s ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                    bs1 { «end» := 3#usize }
                let o ← value.convert.trusted.btou_u32 s
                let i2 ← core.option.Option.unwrap o
                let s1 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                    { start := 4#usize, «end» := 6#usize }
                let o1 ← value.convert.trusted.btou_u8 s1
                let i3 ← core.option.Option.unwrap o1
                let s2 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                    { start := 7#usize, «end» := 9#usize }
                let o2 ← value.convert.trusted.btou_u8 s2
                let i4 ← core.option.Option.unwrap o2
                let o3 ←
                  core.option.Option.map
                    value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                    (some { start := 10#usize }) bs1
                let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
                ok (some (neg, i2, i3, i4, i5))
              else ok none
        else
          let b1 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 2#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 3#usize, «end» := 5#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 6#usize, «end» := 8#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 9#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 3#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 4#usize, «end» := 6#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 7#usize, «end» := 9#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 10#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else ok none
    else
      if len = 9#usize
      then
        let b ← value.convert.trusted.time_re_hhh_mm_ss bs1
        if b
        then
          let s ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
              { «end» := 3#usize }
          let o ← value.convert.trusted.btou_u32 s
          let i2 ← core.option.Option.unwrap o
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 4#usize, «end» := 6#usize }
          let o1 ← value.convert.trusted.btou_u8 s1
          let i3 ← core.option.Option.unwrap o1
          let s2 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 7#usize, «end» := 9#usize }
          let o2 ← value.convert.trusted.btou_u8 s2
          let i4 ← core.option.Option.unwrap o2
          let o3 ←
            core.option.Option.map
              value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
              none bs1
          let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
          ok (some (neg, i2, i3, i4, i5))
        else
          let b1 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 2#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 3#usize, «end» := 5#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 6#usize, «end» := 8#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 9#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 3#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 4#usize, «end» := 6#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 7#usize, «end» := 9#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 10#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else ok none
      else
        let b ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
        if b
        then
          let s ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
              { «end» := 2#usize }
          let o ← value.convert.trusted.btou_u32 s
          let i2 ← core.option.Option.unwrap o
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 3#usize, «end» := 5#usize }
          let o1 ← value.convert.trusted.btou_u8 s1
          let i3 ← core.option.Option.unwrap o1
          let s2 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 6#usize, «end» := 8#usize }
          let o2 ← value.convert.trusted.btou_u8 s2
          let i4 ← core.option.Option.unwrap o2
          let o3 ←
            core.option.Option.map
              value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
              (some { start := 9#usize }) bs1
          let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
          ok (some (neg, i2, i3, i4, i5))
        else
          let b1 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 3#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 4#usize, «end» := 6#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 7#usize, «end» := 9#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 10#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else ok none) ⦃ r => r.map tview = tsrRest neg bs1.val ⦄ := by
  have e1 : value.convert.trusted.time_re_hh_mm_ss bs1 = ok (Trusted.Regex.asciiMatch .timeHhMmSs bs1.val) := by
    simp [value.convert.trusted.time_re_hh_mm_ss, Trusted.isMatch_ascii _ _ ha]
  have e2 : value.convert.trusted.time_re_hh_mm_ss_ms bs1 = ok (Trusted.Regex.asciiMatch .timeHhMmSsMs bs1.val) := by
    simp [value.convert.trusted.time_re_hh_mm_ss_ms, Trusted.isMatch_ascii _ _ ha]
  have e3 : value.convert.trusted.time_re_hhh_mm_ss bs1 = ok (Trusted.Regex.asciiMatch .timeHhhMmSs bs1.val) := by
    simp [value.convert.trusted.time_re_hhh_mm_ss, Trusted.isMatch_ascii _ _ ha]
  have e4 : value.convert.trusted.time_re_hhh_mm_ss_ms bs1 = ok (Trusted.Regex.asciiMatch .timeHhhMmSsMs bs1.val) := by
    simp [value.convert.trusted.time_re_hhh_mm_ss_ms, Trusted.isMatch_ascii _ _ ha]
  simp only [e1, e2, e3, e4, bind_ok]
  have hl : (Slice.len bs1).val = bs1.val.length := by simp
  split_ifs
  all_goals try first
    | exact leaf_hh bs1 neg ‹_›
    | exact leaf_hhh bs1 neg ‹_›
    | exact leaf_hh_ms bs1 neg ‹_›
    | exact leaf_hhh_ms bs1 neg ‹_›
  all_goals
    simp only [WP.spec_ok, Option.map_none]
    symm; by_contra hne
    rcases tsr_some neg bs1.val hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h2 | h2
  all_goals (simp only [UScalar.eq_equiv, hl] at *; simp_all)

/-- The parser on ASCII input. -/
private theorem spec_ascii (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_time_string b ⦃ r =>
      r.map (fun t => (t.1, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.val)) =
        timeStringRead b.val ⦄ := by
  unfold value.convert.parse_mysql_time_string
  dsimp only
  split
  · rename_i hlt
    have hl : b.val.length < 8 := by simp only [UScalar.lt_equiv, Slice.len_val] at hlt; simpa [Slice.length] using hlt
    simp only [WP.spec_ok, Option.map_none]
    cases hb : b.val with
    | nil => rfl
    | cons c rest =>
      rw [hb] at hl
      rw [timeStringRead_cons]
      split
      · by_contra hne; have := tsrRest_len _ _ (Ne.symm hne); simp at hl this; omega
      · by_contra hne; have := tsrRest_len _ _ (Ne.symm hne); simp at hl this; omega
  · rename_i hge
    have hl : 8 ≤ b.val.length := by
      simp only [UScalar.lt_equiv, Slice.len_val, not_lt] at hge; simpa [Slice.length] using hge
    obtain ⟨c, rest, hb⟩ : ∃ c rest, b.val = c :: rest := by
      cases h : b.val with
      | nil => rw [h] at hl; simp at hl
      | cons c rest => exact ⟨c, rest, rfl⟩
    step
    have hi1 : i1 = c := by simp_all
    split
    · rename_i hc
      step
      apply WP.spec_mono (core_spec _ _ ?_)
      · intro r hr
        change Option.map tview r = _
        rw [hr, hb, timeStringRead_cons]
        have : c.val = 45 := by rw [← hi1, hc]; rfl
        simp [this, hc, bytes1_post, hb]
      · intro x hx; rw [bytes1_post, hb] at hx; exact ha x (by simp [hb]; right; simpa using hx)
    · rename_i hc
      have hcs := core_spec b (decide (i1 = 45#u8)) ha
      simp only [bind_ok]
      refine WP.spec_mono hcs ?_
      intro r hr
      change Option.map tview r = _
      rw [hr, hb, timeStringRead_cons]
      have : ¬ c.val = 45 := by
        intro e; apply hc; rw [hi1]; exact UScalar.eq_of_val_eq (by simpa using e)
      simp [this, hc]

/-! ### Input with a non-ASCII byte -/

/-- The input after its optional sign. -/
private def unsigned (bs : List U8) : List U8 :=
  match bs with
  | c :: rest => if c.val = 45 then rest else bs
  | [] => []

private theorem unsigned_nonascii (bs : List U8) (hn : ∃ c ∈ bs, 128 ≤ c.val) :
    ∃ c ∈ unsigned bs, 128 ≤ c.val := by
  obtain ⟨c, hc, hc'⟩ := hn
  match bs with
  | [] => simp at hc
  | c0 :: rest =>
    simp only [unsigned]
    split_ifs with h
    · rcases List.mem_cons.1 hc with rfl | hc
      · omega
      · exact ⟨c, hc, hc'⟩
    · exact ⟨c, hc, hc'⟩

private theorem unsigned_length (bs : List U8) : (unsigned bs).length ≤ bs.length := by
  match bs with
  | [] => simp [unsigned]
  | c0 :: rest => simp only [unsigned]; split_ifs <;> simp

/-- `timeStringRead` rejects every input with a non-ASCII byte. -/
theorem timeStringRead_nonascii (bs : List U8) (hn : ∃ c ∈ bs, 128 ≤ c.val) :
    timeStringRead bs = none := by
  obtain ⟨c, hc, hc'⟩ := unsigned_nonascii bs hn
  have key : ∀ neg, tsrRest neg (unsigned bs) = none := by
    intro neg
    by_contra hne
    rcases tsr_some neg _ hne with ⟨-, h⟩ | ⟨-, h⟩ | h | h <;>
      have := asciiMatch_ascii _ _ h c hc <;> omega
  match bs with
  | [] => rfl
  | c0 :: rest =>
    rw [timeStringRead_cons]
    simp only [unsigned] at key
    split_ifs with h
    · simpa [h] using key true
    · simpa [h] using key false

/-- `timeTextPanics` is false of ASCII input. -/
theorem not_timeTextPanics_of_ascii (bs : List U8) (ha : ∀ c ∈ bs, c.val < 128) :
    ¬ timeTextPanics bs := by
  rintro ⟨⟨c, hc, hc'⟩, -⟩
  have := ha c hc; omega

/-- `timeTextPanics` is false of input of at most 10 bytes: a fractional form holding a
    non-ASCII digit is at least 11 bytes long. -/
theorem not_timeTextPanics_of_length (bs : List U8) (hl : bs.length ≤ 10) :
    ¬ timeTextPanics bs := by
  rintro ⟨hn, t, ht, hm⟩
  have hu := unsigned_nonascii bs hn
  have hlen := unsigned_length bs
  rw [show unsigned bs = t.val from ht.symm] at hu hlen
  rcases hm with hm | hm <;>
    have := isMatch_nonascii_length _ t hm hu <;> simp only [minLen] at this <;> omega

/-- The parser after the sign. -/
private noncomputable def tcore (bs1 : Slice U8) (neg : Bool) :
    Result (Option (Bool × Std.U32 × Std.U8 × Std.U8 × Std.U32)) :=
    (do
    let len := Slice.len bs1
    if len = 8#usize
    then
      let b ← value.convert.trusted.time_re_hh_mm_ss bs1
      if b
      then
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            none bs1
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))
      else
        if len = 9#usize
        then
          let b1 ← value.convert.trusted.time_re_hhh_mm_ss bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 3#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 4#usize, «end» := 6#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 7#usize, «end» := 9#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                none bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 2#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 3#usize, «end» := 5#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 6#usize, «end» := 8#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 9#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else
              let b3 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
              if b3
              then
                let s ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                    bs1 { «end» := 3#usize }
                let o ← value.convert.trusted.btou_u32 s
                let i2 ← core.option.Option.unwrap o
                let s1 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                    { start := 4#usize, «end» := 6#usize }
                let o1 ← value.convert.trusted.btou_u8 s1
                let i3 ← core.option.Option.unwrap o1
                let s2 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                    { start := 7#usize, «end» := 9#usize }
                let o2 ← value.convert.trusted.btou_u8 s2
                let i4 ← core.option.Option.unwrap o2
                let o3 ←
                  core.option.Option.map
                    value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                    (some { start := 10#usize }) bs1
                let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
                ok (some (neg, i2, i3, i4, i5))
              else ok none
        else
          let b1 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 2#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 3#usize, «end» := 5#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 6#usize, «end» := 8#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 9#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 3#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 4#usize, «end» := 6#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 7#usize, «end» := 9#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 10#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else ok none
    else
      if len = 9#usize
      then
        let b ← value.convert.trusted.time_re_hhh_mm_ss bs1
        if b
        then
          let s ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
              { «end» := 3#usize }
          let o ← value.convert.trusted.btou_u32 s
          let i2 ← core.option.Option.unwrap o
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 4#usize, «end» := 6#usize }
          let o1 ← value.convert.trusted.btou_u8 s1
          let i3 ← core.option.Option.unwrap o1
          let s2 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 7#usize, «end» := 9#usize }
          let o2 ← value.convert.trusted.btou_u8 s2
          let i4 ← core.option.Option.unwrap o2
          let o3 ←
            core.option.Option.map
              value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
              none bs1
          let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
          ok (some (neg, i2, i3, i4, i5))
        else
          let b1 ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 2#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 3#usize, «end» := 5#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 6#usize, «end» := 8#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 9#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else
            let b2 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
            if b2
            then
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                  { «end» := 3#usize }
              let o ← value.convert.trusted.btou_u32 s
              let i2 ← core.option.Option.unwrap o
              let s1 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 4#usize, «end» := 6#usize }
              let o1 ← value.convert.trusted.btou_u8 s1
              let i3 ← core.option.Option.unwrap o1
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                  { start := 7#usize, «end» := 9#usize }
              let o2 ← value.convert.trusted.btou_u8 s2
              let i4 ← core.option.Option.unwrap o2
              let o3 ←
                core.option.Option.map
                  value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                  (some { start := 10#usize }) bs1
              let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
              ok (some (neg, i2, i3, i4, i5))
            else ok none
      else
        let b ← value.convert.trusted.time_re_hh_mm_ss_ms bs1
        if b
        then
          let s ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
              { «end» := 2#usize }
          let o ← value.convert.trusted.btou_u32 s
          let i2 ← core.option.Option.unwrap o
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 3#usize, «end» := 5#usize }
          let o1 ← value.convert.trusted.btou_u8 s1
          let i3 ← core.option.Option.unwrap o1
          let s2 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
              { start := 6#usize, «end» := 8#usize }
          let o2 ← value.convert.trusted.btou_u8 s2
          let i4 ← core.option.Option.unwrap o2
          let o3 ←
            core.option.Option.map
              value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
              (some { start := 9#usize }) bs1
          let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
          ok (some (neg, i2, i3, i4, i5))
        else
          let b1 ← value.convert.trusted.time_re_hhh_mm_ss_ms bs1
          if b1
          then
            let s ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bs1
                { «end» := 3#usize }
            let o ← value.convert.trusted.btou_u32 s
            let i2 ← core.option.Option.unwrap o
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 4#usize, «end» := 6#usize }
            let o1 ← value.convert.trusted.btou_u8 s1
            let i3 ← core.option.Option.unwrap o1
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bs1
                { start := 7#usize, «end» := 9#usize }
            let o2 ← value.convert.trusted.btou_u8 s2
            let i4 ← core.option.Option.unwrap o2
            let o3 ←
              core.option.Option.map
                value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
                (some { start := 10#usize }) bs1
            let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
            ok (some (neg, i2, i3, i4, i5))
          else ok none)

private theorem hhms_block_panic (b : Slice U8) (neg : Bool)
    (h : ∃ (i : Nat) (x : U8), b.val[i]? = some x ∧ 128 ≤ x.val ∧ i ≠ 2 ∧ i ≠ 5 ∧ i ≠ 8) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 2#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 3#usize, «end» := 5#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 6#usize, «end» := 8#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            (some { start := 9#usize }) b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) = fail .panic := by
  have key : (do
      let i2 ← fldTo32 b { «end» := 2#usize }
      let i3 ← fld8 b { start := 3#usize, «end» := 5#usize }
      let i4 ← fld8 b { start := 6#usize, «end» := 8#usize }
      let i5 ← fldMicros b { start := 9#usize }
      ok (some (neg, i2, i3, i4, i5))) = fail .panic := by
    obtain ⟨i, x, hx, hx', n2, n5, n8⟩ := h
    have hc : i < 2 ∨ (3 ≤ i ∧ i < 5) ∨ (6 ≤ i ∧ i < 8) ∨ 9 ≤ i := by omega
    rcases hc with c | c | c | c
    · exact bind_p (fldTo32_panic b _ i x hx hx' c)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_p (fld8_panic b _ i x hx hx' c.1 c.2)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_okp (fld8_okp _ _) fun _ =>
        bind_p (fld8_panic b _ i x hx hx' c.1 c.2)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_okp (fld8_okp _ _) fun _ =>
        bind_okp (fld8_okp _ _) fun _ => bind_p (fldMicros_panic b _ i x hx hx' c)
  simpa only [fldTo32, fld8, fldMicros, tc_bind_eq, Aeneas.Std.bind_assoc,
    core.option.Option.map_some,
    value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32.call_once,
    lift, bind_ok, core.option.Option.unwrap_or_some] using key

private theorem hhhms_block_panic (b : Slice U8) (neg : Bool)
    (h : ∃ (i : Nat) (x : U8), b.val[i]? = some x ∧ 128 ≤ x.val ∧ i ≠ 3 ∧ i ≠ 6 ∧ i ≠ 9) :
    (do
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
            { «end» := 3#usize }
        let o ← value.convert.trusted.btou_u32 s
        let i2 ← core.option.Option.unwrap o
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 4#usize, «end» := 6#usize }
        let o1 ← value.convert.trusted.btou_u8 s1
        let i3 ← core.option.Option.unwrap o1
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
            { start := 7#usize, «end» := 9#usize }
        let o2 ← value.convert.trusted.btou_u8 s2
        let i4 ← core.option.Option.unwrap o2
        let o3 ←
          core.option.Option.map
            value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
            (some { start := 10#usize }) b
        let i5 ← lift (core.option.Option.unwrap_or o3 0#u32)
        ok (some (neg, i2, i3, i4, i5))) = fail .panic := by
  have key : (do
      let i2 ← fldTo32 b { «end» := 3#usize }
      let i3 ← fld8 b { start := 4#usize, «end» := 6#usize }
      let i4 ← fld8 b { start := 7#usize, «end» := 9#usize }
      let i5 ← fldMicros b { start := 10#usize }
      ok (some (neg, i2, i3, i4, i5))) = fail .panic := by
    obtain ⟨i, x, hx, hx', n3, n6, n9⟩ := h
    have hc : i < 3 ∨ (4 ≤ i ∧ i < 6) ∨ (7 ≤ i ∧ i < 9) ∨ 10 ≤ i := by omega
    rcases hc with c | c | c | c
    · exact bind_p (fldTo32_panic b _ i x hx hx' c)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_p (fld8_panic b _ i x hx hx' c.1 c.2)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_okp (fld8_okp _ _) fun _ =>
        bind_p (fld8_panic b _ i x hx hx' c.1 c.2)
    · exact bind_okp (fldTo32_okp _ _) fun _ => bind_okp (fld8_okp _ _) fun _ =>
        bind_okp (fld8_okp _ _) fun _ => bind_p (fldMicros_panic b _ i x hx hx' c)
  simpa only [fldTo32, fld8, fldMicros, tc_bind_eq, Aeneas.Std.bind_assoc,
    core.option.Option.map_some,
    value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32.call_once,
    lift, bind_ok, core.option.Option.unwrap_or_some] using key

/-- After the sign, on input with a non-ASCII byte: a panic if a fractional regex matches,
    `None` otherwise (the two fixed-length forms cannot match). -/
private theorem tcore_nonascii (t : Slice U8) (neg : Bool) (hn : ∃ c ∈ t.val, 128 ≤ c.val) :
    tcore t neg =
      if Trusted.isMatch .timeHhMmSsMs t = true ∨ Trusted.isMatch .timeHhhMmSsMs t = true
      then fail .panic else ok none := by
  have m1 : Slice.len t = 8#usize → Trusted.isMatch .timeHhMmSs t = false := by
    intro hl; by_contra hm
    have := isMatch_nonascii_length _ t (by simpa using hm) hn
    simp only [minLen] at this; scalar_tac
  have m2 : Slice.len t = 9#usize → Trusted.isMatch .timeHhhMmSs t = false := by
    intro hl; by_contra hm
    have := isMatch_nonascii_length _ t (by simpa using hm) hn
    simp only [minLen] at this; scalar_tac
  unfold tcore
  simp only [value.convert.trusted.time_re_hh_mm_ss, value.convert.trusted.time_re_hh_mm_ss_ms,
    value.convert.trusted.time_re_hhh_mm_ss, value.convert.trusted.time_re_hhh_mm_ss_ms, bind_ok]
  have hlen : (Slice.len t = 8#usize ∧ ¬ Slice.len t = 9#usize) ∨
      (¬ Slice.len t = 8#usize ∧ Slice.len t = 9#usize) ∨
      (¬ Slice.len t = 8#usize ∧ ¬ Slice.len t = 9#usize) := by
    by_cases c8 : Slice.len t = 8#usize
    · exact Or.inl ⟨c8, by rw [c8]; decide⟩
    · by_cases c9 : Slice.len t = 9#usize
      · exact Or.inr (Or.inl ⟨c8, c9⟩)
      · exact Or.inr (Or.inr ⟨c8, c9⟩)
  cases hA : Trusted.isMatch .timeHhMmSsMs t
  · cases hB : Trusted.isMatch .timeHhhMmSsMs t
    · rcases hlen with ⟨c8, c9⟩ | ⟨c8, c9⟩ | ⟨c8, c9⟩
      · simp only [eq_true c8, c9, m1 c8, ↓reduceIte, Bool.false_eq_true, or_self]
      · simp only [c8, eq_true c9, m2 c9, ↓reduceIte, Bool.false_eq_true, or_self]
      · simp only [c8, c9, ↓reduceIte, Bool.false_eq_true, or_self]
    · have hpos := hhhms_nonascii_pos t hB hn
      rcases hlen with ⟨c8, c9⟩ | ⟨c8, c9⟩ | ⟨c8, c9⟩
      · simp only [eq_true c8, c9, m1 c8, ↓reduceIte, Bool.false_eq_true, or_true]
        exact hhhms_block_panic t neg hpos
      · simp only [c8, eq_true c9, m2 c9, ↓reduceIte, Bool.false_eq_true, or_true]
        exact hhhms_block_panic t neg hpos
      · simp only [c8, c9, ↓reduceIte, Bool.false_eq_true, or_true]
        exact hhhms_block_panic t neg hpos
  · have hpos := hhms_nonascii_pos t hA hn
    rcases hlen with ⟨c8, c9⟩ | ⟨c8, c9⟩ | ⟨c8, c9⟩
    · simp only [eq_true c8, c9, m1 c8, ↓reduceIte, Bool.false_eq_true, true_or]
      exact hhms_block_panic t neg hpos
    · simp only [c8, eq_true c9, m2 c9, ↓reduceIte, Bool.false_eq_true, true_or]
      exact hhms_block_panic t neg hpos
    · simp only [c8, c9, ↓reduceIte, true_or]
      exact hhms_block_panic t neg hpos

/-- From 8 bytes on, the parser is `tcore` of the input after its sign. -/
private theorem parse_eq_tcore (b : Slice U8) (h8 : 8 ≤ b.val.length) :
    ∃ t : Slice U8, t.val = unsigned b.val ∧
      ∃ neg, value.convert.parse_mysql_time_string b = tcore t neg := by
  obtain ⟨c, rest, hb⟩ : ∃ c rest, b.val = c :: rest := by
    cases h : b.val with
    | nil => rw [h] at h8; simp at h8
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hlt : ¬ (Slice.len b < 8#usize) := by scalar_tac
  have hidx : Slice.index_usize b 0#usize = ok c := by
    simp [Slice.index_usize, hb]
  unfold value.convert.parse_mysql_time_string
  simp only [hlt, ↓reduceIte, hidx, bind_ok]
  by_cases hc : c = 45#u8
  · have hd : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) b
        { start := 1#usize } = ok (b.drop 1#usize) := by
      simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index,
        Slice.length, hb]
    rw [ite_pos' hc, hd]
    simp only [bind_ok]
    refine ⟨b.drop 1#usize, ?_, decide (c = 45#u8), rfl⟩
    simp [unsigned, hb, hc]
  · rw [ite_neg' hc]
    simp only [bind_ok]
    refine ⟨b, ?_, decide (c = 45#u8), rfl⟩
    have : ¬ c.val = 45 := fun e => hc (UScalar.eq_of_val_eq (by simpa using e))
    simp [unsigned, hb, this]

/-- `parse_mysql_time_string` (private, used by the `Duration`, chrono and time conversions), on
    every input on which it does not panic (`timeTextPanics`; in particular on all ASCII input
    and on all input of at most 10 bytes): the text `TIME` literal `timeStringRead`, as
    `(negative, hours, minutes, seconds, microseconds)`. An input with a non-ASCII byte is never
    read as a time: `timeStringRead` is `none` on it (`timeStringRead_nonascii`). -/
theorem value.convert.parse_mysql_time_string_spec (b : Slice U8) (hp : ¬ timeTextPanics b.val) :
    value.convert.parse_mysql_time_string b ⦃ r =>
      r.map (fun t => (t.1, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.val)) =
        timeStringRead b.val ⦄ := by
  by_cases ha : ∀ c ∈ b.val, c.val < 128
  · exact spec_ascii b ha
  have hn : ∃ c ∈ b.val, 128 ≤ c.val := by
    by_contra hc; exact ha fun c hc' => by by_contra h; exact hc ⟨c, hc', by omega⟩
  rw [timeStringRead_nonascii _ hn]
  by_cases h8 : 8 ≤ b.val.length
  · obtain ⟨t, ht, neg, he⟩ := parse_eq_tcore b h8
    rw [he, tcore_nonascii t neg (ht ▸ unsigned_nonascii _ hn),
      ite_neg' (fun hm => hp ⟨hn, t, ht, hm⟩)]
    simp
  · have hlt : Slice.len b < 8#usize := by scalar_tac
    unfold value.convert.parse_mysql_time_string
    simp only [hlt, ↓reduceIte]
    simp

/-- **Crash path.** `parse_mysql_time_string` panics exactly on `timeTextPanics`: an input with
    a non-ASCII byte that, after its sign, a fractional regex matches (its Unicode `\d` matched
    a non-ASCII digit), because `btou(..).unwrap()` rejects the field holding it. E.g.
    `"00:00:00.\u{0660}"`, if the regex matches it (which is not modelled). -/
theorem value.convert.parse_mysql_time_string_panic (b : Slice U8) (hp : timeTextPanics b.val) :
    value.convert.parse_mysql_time_string b = fail .panic := by
  obtain ⟨hn, t, ht, hm⟩ := hp
  have hu : ∃ c ∈ t.val, 128 ≤ c.val := ht ▸ unsigned_nonascii _ hn
  have h8 : 8 ≤ b.val.length := by
    have hlen := unsigned_length b.val
    rw [show unsigned b.val = t.val from ht.symm] at hlen
    rcases hm with hm | hm <;>
      have := isMatch_nonascii_length _ t hm hu <;> simp only [minLen] at this <;> omega
  obtain ⟨t', ht', neg, he⟩ := parse_eq_tcore b h8
  have : t' = t := Slice.ext _ _ (ht'.trans ht.symm)
  rw [he, this, tcore_nonascii t neg hu, ite_pos' hm]

end mysql_common
