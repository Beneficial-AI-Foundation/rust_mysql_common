import Defs
import Proofs.Util.ConvBytesTime

/-! Statements for `fn parse_mysql_time_string` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

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

/-- `parse_mysql_time_string` (private, used by the `Duration`, chrono and time conversions): on
    ASCII input, total; the text `TIME` literal `timeStringRead`, as `(negative, hours, minutes,
    seconds, microseconds)`. **ASCII hypothesis:** on non-ASCII input the Unicode-mode regexes
    can match non-ASCII digits and `btou(..).unwrap()` panics,
    e.g. on `"00:00:00.\u{0660}"`; the regexes are only specified on ASCII input, so that case is
    excluded rather than stated. -/

theorem value.convert.parse_mysql_time_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
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

end mysql_common
