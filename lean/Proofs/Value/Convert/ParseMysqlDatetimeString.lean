import Defs
import Proofs.Util.ConvBytesTime

/-! Statements for `fn parse_mysql_datetime_string` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

namespace mysql_common

@[step]
private theorem closure_map_spec (R : Option (core.ops.range.Range Usize)) (b : Slice U8)
    (h : ∀ r : core.ops.range.Range Usize, R = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9) :
    core.option.Option.map value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32 R b ⦃ o =>
      o.map (·.val) = R.map (fun r => digitsVal (b.val.slice r.start.val r.end.val)) ⦄ := by
  cases R with
  | none => simp
  | some r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h r rfl
    simp only [core.option.Option.map, value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32.call_once]
    apply WP.spec_bind (Pₘ := fun v : U32 => v.val = digitsVal (b.val.slice r.start.val r.end.val))
    · step*
    · intro v hv; simp [hv]

@[step]
private theorem closure_1_map_spec (R : Option (core.ops.range.Range Usize)) (b : Slice U8)
    (h : ∀ r : core.ops.range.Range Usize, R = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9) :
    core.option.Option.map value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32 R b ⦃ o =>
      o.map (·.val) = R.map (fun r => digitsVal (b.val.slice r.start.val r.end.val)) ⦄ := by
  cases R with
  | none => simp
  | some r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h r rfl
    simp only [core.option.Option.map, value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32.call_once]
    apply WP.spec_bind (Pₘ := fun v : U32 => v.val = digitsVal (b.val.slice r.start.val r.end.val))
    · step*
    · intro v hv; simp [hv]

@[step]
private theorem closure_2_map_spec (R : Option (core.ops.range.Range Usize)) (b : Slice U8)
    (h : ∀ r : core.ops.range.Range Usize, R = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9) :
    core.option.Option.map value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32 R b ⦃ o =>
      o.map (·.val) = R.map (fun r => digitsVal (b.val.slice r.start.val r.end.val)) ⦄ := by
  cases R with
  | none => simp
  | some r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h r rfl
    simp only [core.option.Option.map, value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32.call_once]
    apply WP.spec_bind (Pₘ := fun v : U32 => v.val = digitsVal (b.val.slice r.start.val r.end.val))
    · step*
    · intro v hv; simp [hv]

@[step]
private theorem closure_3_map_spec (M : Option (core.ops.range.RangeFrom Usize)) (b : Slice U8)
    (h : ∀ st : core.ops.range.RangeFrom Usize, M = some st → st.start.val ≤ b.length ∧
      b.val.drop st.start.val ≠ [] ∧ (b.val.drop st.start.val).all isDigit ∧
      (b.val.drop st.start.val).length ≤ 6) :
    core.option.Option.map value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32 M b ⦃ o => o.map (·.val) = M.map (fun st => fracVal (b.val.drop st.start.val)) ⦄ := by
  cases M with
  | none => simp
  | some st =>
    obtain ⟨h1, h2, h3, h4⟩ := h st rfl
    simp only [core.option.Option.map, value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32.call_once]
    apply WP.spec_bind (Pₘ := fun v : U32 => v.val = fracVal (b.val.drop st.start.val))
    · step*
      simp_all [fracVal]
    · intro v hv; simp [hv]

private theorem uo_val {α : Type} (o : Option U32) (X : Option α) (f : α → Nat)
    (h : o.map (·.val) = X.map f) : (core.option.Option.unwrap_or o 0#u32).val = (X.map f).getD 0 := by
  cases o <;> cases X <;> simp_all [core.option.Option.unwrap_or]

/-- The field-reading block of `parse_mysql_datetime_string`. -/
private theorem dt_block_spec (b : Slice U8) (H Mi S : Option (core.ops.range.Range Usize))
    (Mic : Option (core.ops.range.RangeFrom Usize))
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U8) (rest : List U8)
    (hb : b.val = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: rest)
    (hd : isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a3 ∧ isDigit a5 ∧ isDigit a6 ∧
      isDigit a8 ∧ isDigit a9)
    (hH : ∀ r : core.ops.range.Range Usize, H = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9)
    (hMi : ∀ r : core.ops.range.Range Usize, Mi = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9)
    (hS : ∀ r : core.ops.range.Range Usize, S = some r → r.start.val ≤ r.end.val ∧
      r.end.val ≤ b.length ∧ b.val.slice r.start.val r.end.val ≠ [] ∧
      (b.val.slice r.start.val r.end.val).all isDigit ∧ (b.val.slice r.start.val r.end.val).length ≤ 9)
    (hM : ∀ st : core.ops.range.RangeFrom Usize, Mic = some st → st.start.val ≤ b.length ∧
      b.val.drop st.start.val ≠ [] ∧ (b.val.drop st.start.val).all isDigit ∧
      (b.val.drop st.start.val).length ≤ 6) :
    (do
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
          { «end» := 4#usize }
      let o ← value.convert.trusted.btou_u32 s
      let i ← core.option.Option.unwrap o
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 5#usize, «end» := 7#usize }
      let o1 ← value.convert.trusted.btou_u32 s1
      let i1 ← core.option.Option.unwrap o1
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 8#usize, «end» := 10#usize }
      let o2 ← value.convert.trusted.btou_u32 s2
      let i2 ← core.option.Option.unwrap o2
      let o3 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          H b
      let i3 ← lift (core.option.Option.unwrap_or o3 0#u32)
      let o4 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          Mi b
      let i4 ← lift (core.option.Option.unwrap_or o4 0#u32)
      let o5 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          S b
      let i5 ← lift (core.option.Option.unwrap_or o5 0#u32)
      let o6 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
          Mic b
      let i6 ← lift (core.option.Option.unwrap_or o6 0#u32)
      ok (some (i, i1, i2, i3, i4, i5, i6))) ⦃ r =>
      ∃ y mo d h mi sec us, r = some (y, mo, d, h, mi, sec, us) ∧ y.val = digitsVal [a0, a1, a2, a3] ∧
        mo.val = digitsVal [a5, a6] ∧ d.val = digitsVal [a8, a9] ∧
        h.val = (H.map fun r => digitsVal (b.val.slice r.start.val r.end.val)).getD 0 ∧ mi.val = (Mi.map fun r => digitsVal (b.val.slice r.start.val r.end.val)).getD 0 ∧
        sec.val = (S.map fun r => digitsVal (b.val.slice r.start.val r.end.val)).getD 0 ∧
        us.val = (Mic.map fun st => fracVal (b.val.drop st.start.val)).getD 0 ⦄ := by
  obtain ⟨d0, d1, d2, d3, d5, d6, d8, d9⟩ := hd
  step*
  all_goals clear hH hMi hS hM
  on_goal 7 =>
    refine ⟨_, _, _, _, _, _, _, rfl, ?_, ?_, ?_, (i3_post ▸ uo_val _ _ _ o3_post), (i4_post ▸ uo_val _ _ _ o4_post),
      (i5_post ▸ uo_val _ _ _ o5_post), (i6_post ▸ uo_val _ _ _ o6_post)⟩
  all_goals simp_all [List.slice, Slice.length]

/-- What the parser returns, as `(year, month, day, hour, minute, second, microsecond)`. -/
private def dview (t : U32 × U32 × U32 × U32 × U32 × U32 × U32) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (t.1.val, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.1.val, t.2.2.2.2.2.1.val, t.2.2.2.2.2.2.val)

private theorem dsr_ymd (t : List U8) (hR : Trusted.Regex.asciiMatch .datetimeYmd t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U8, t = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a3 ∧ isDigit a5 ∧ isDigit a6 ∧ isDigit a8 ∧ isDigit a9) ∧
      datetimeStringRead t = some (digitsVal [a0, a1, a2, a3], digitsVal [a5, a6], digitsVal [a8, a9], 0, 0, 0, 0) := by
  match t with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] =>
    simp only [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.matchSeq, Trusted.digit, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl, ?_, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]
    · simp_all [datetimeStringRead, allDigits, isDigit, Trusted.isAsciiDigit]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _] => simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.matchSeq] at hR
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.matchSeq] at hR

private theorem dsr_ymdhms (t : List U8) (hR : Trusted.Regex.asciiMatch .datetimeYmdHms t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : U8, t = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18] ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a3 ∧ isDigit a5 ∧ isDigit a6 ∧ isDigit a8 ∧ isDigit a9 ∧
        isDigit a11 ∧ isDigit a12 ∧ isDigit a14 ∧ isDigit a15 ∧ isDigit a17 ∧ isDigit a18) ∧
      datetimeStringRead t = some (digitsVal [a0, a1, a2, a3], digitsVal [a5, a6], digitsVal [a8, a9],
        digitsVal [a11, a12], digitsVal [a14, a15], digitsVal [a17, a18], 0) := by
  match t with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18] =>
    simp only [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, List.cons_append, List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, rfl, ?_, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]
    · simp_all [datetimeStringRead, allDigits, isDigit, Trusted.isAsciiDigit, fracRead]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, Trusted.matchSeq] at hR
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, Trusted.matchSeq] at hR

private theorem dmatchFrac (l : List U8) (h : Trusted.matchFrac l = true) :
    ∃ c ds, l = c :: ds ∧ c.val = 46 ∧ ds ≠ [] ∧ ds.all isDigit ∧ ds.length ≤ 6 := by
  match l with
  | [] => simp [Trusted.matchFrac] at h
  | c :: ds =>
    simp only [Trusted.matchFrac, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨c, ds, rfl, h.1.1.1, ?_, ?_, h.1.2⟩
    · intro e; subst e; simp at h
    · simpa [isAsciiDigit_eq] using h.2

private theorem dfracRead_dot (c : U8) (ds : List U8) (hc : c.val = 46) (h1 : ds ≠ [])
    (h2 : ds.all isDigit) (h3 : ds.length ≤ 6) : fracRead (c :: ds) = some (fracVal ds) := by
  have : 1 ≤ ds.length := by cases ds <;> simp_all
  simp [fracRead, hc, h2, h3, this, fracVal]

private theorem dsr_ns (t : List U8) (hR : Trusted.Regex.asciiMatch .datetimeYmdHmsNs t = true) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : U8, ∃ ds : List U8, t = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: ds ∧
      (isDigit a0 ∧ isDigit a1 ∧ isDigit a2 ∧ isDigit a3 ∧ isDigit a5 ∧ isDigit a6 ∧ isDigit a8 ∧ isDigit a9 ∧
        isDigit a11 ∧ isDigit a12 ∧ isDigit a14 ∧ isDigit a15 ∧ isDigit a17 ∧ isDigit a18) ∧
      (ds ≠ [] ∧ ds.all isDigit ∧ ds.length ≤ 6) ∧
      datetimeStringRead t = some (digitsVal [a0, a1, a2, a3], digitsVal [a5, a6], digitsVal [a8, a9],
        digitsVal [a11, a12], digitsVal [a14, a15], digitsVal [a17, a18], fracVal ds) := by
  match t with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: rest =>
    simp only [Trusted.Regex.asciiMatch, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, Bool.and_eq_true] at hR
    obtain ⟨hR, hF⟩ := hR
    obtain ⟨a19, ds, rfl, h19, hd1, hd2, hd3⟩ := dmatchFrac rest hF
    simp only [Trusted.ymd, Trusted.ymdHms, List.cons_append, List.nil_append, Trusted.matchSeq, Trusted.digit, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq, Bool.and_true] at hR
    refine ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, ds, rfl, ?_, ⟨hd1, hd2, hd3⟩, ?_⟩
    · simp_all [isDigit, Trusted.isAsciiDigit]
    · have hf := dfracRead_dot a19 ds h19 hd1 hd2 hd3
      simp only [datetimeStringRead]
      simp_all [allDigits, isDigit, Trusted.isAsciiDigit]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, Trusted.matchSeq] at hR

private theorem leaf_ymd (b : Slice U8) (hR : Trusted.Regex.asciiMatch .datetimeYmd b.val = true) :
    (do
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
          { «end» := 4#usize }
      let o ← value.convert.trusted.btou_u32 s
      let i ← core.option.Option.unwrap o
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 5#usize, «end» := 7#usize }
      let o1 ← value.convert.trusted.btou_u32 s1
      let i1 ← core.option.Option.unwrap o1
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 8#usize, «end» := 10#usize }
      let o2 ← value.convert.trusted.btou_u32 s2
      let i2 ← core.option.Option.unwrap o2
      let o3 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          none b
      let i3 ← lift (core.option.Option.unwrap_or o3 0#u32)
      let o4 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          none b
      let i4 ← lift (core.option.Option.unwrap_or o4 0#u32)
      let o5 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          none b
      let i5 ← lift (core.option.Option.unwrap_or o5 0#u32)
      let o6 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
          none b
      let i6 ← lift (core.option.Option.unwrap_or o6 0#u32)
      ok (some (i, i1, i2, i3, i4, i5, i6))) ⦃ r => r.map dview = datetimeStringRead b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, ht, hd, hv⟩ := dsr_ymd _ hR
  apply WP.spec_mono (dt_block_spec b none none none none a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 [] (by simp [ht]) hd
    (by simp) (by simp) (by simp) (by simp))
  rintro r ⟨y, mo, d, h, mi, sec, us, rfl, e1, e2, e3, e4, e5, e6, e7⟩
  rw [hv]; simp [dview, e1, e2, e3, e4, e5, e6, e7]

private theorem leaf_ymdhms (b : Slice U8) (hR : Trusted.Regex.asciiMatch .datetimeYmdHms b.val = true) :
    (do
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
          { «end» := 4#usize }
      let o ← value.convert.trusted.btou_u32 s
      let i ← core.option.Option.unwrap o
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 5#usize, «end» := 7#usize }
      let o1 ← value.convert.trusted.btou_u32 s1
      let i1 ← core.option.Option.unwrap o1
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 8#usize, «end» := 10#usize }
      let o2 ← value.convert.trusted.btou_u32 s2
      let i2 ← core.option.Option.unwrap o2
      let o3 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 11#usize, «end» := 13#usize }) b
      let i3 ← lift (core.option.Option.unwrap_or o3 0#u32)
      let o4 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 14#usize, «end» := 16#usize }) b
      let i4 ← lift (core.option.Option.unwrap_or o4 0#u32)
      let o5 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 17#usize, «end» := 19#usize }) b
      let i5 ← lift (core.option.Option.unwrap_or o5 0#u32)
      let o6 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
          none b
      let i6 ← lift (core.option.Option.unwrap_or o6 0#u32)
      ok (some (i, i1, i2, i3, i4, i5, i6))) ⦃ r => r.map dview = datetimeStringRead b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, ht, hd, hv⟩ := dsr_ymdhms _ hR
  obtain ⟨d0, d1, d2, d3, d5, d6, d8, d9, d11, d12, d14, d15, d17, d18⟩ := hd
  apply WP.spec_mono (dt_block_spec b _ _ _ none a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 [a10, a11, a12, a13, a14, a15, a16, a17, a18] (by simp [ht])
    ⟨d0, d1, d2, d3, d5, d6, d8, d9⟩
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d11, d12])
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d14, d15])
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d17, d18]) (by simp))
  rintro r ⟨y, mo, d, h, mi, sec, us, rfl, e1, e2, e3, e4, e5, e6, e7⟩
  rw [hv]; simp [dview, e1, e2, e3, e4, e5, e6, e7, ht, List.slice]

private theorem leaf_ns (b : Slice U8) (hR : Trusted.Regex.asciiMatch .datetimeYmdHmsNs b.val = true) :
    (do
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
          { «end» := 4#usize }
      let o ← value.convert.trusted.btou_u32 s
      let i ← core.option.Option.unwrap o
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 5#usize, «end» := 7#usize }
      let o1 ← value.convert.trusted.btou_u32 s1
      let i1 ← core.option.Option.unwrap o1
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
          { start := 8#usize, «end» := 10#usize }
      let o2 ← value.convert.trusted.btou_u32 s2
      let i2 ← core.option.Option.unwrap o2
      let o3 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 11#usize, «end» := 13#usize }) b
      let i3 ← lift (core.option.Option.unwrap_or o3 0#u32)
      let o4 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_1.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 14#usize, «end» := 16#usize }) b
      let i4 ← lift (core.option.Option.unwrap_or o4 0#u32)
      let o5 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_2.Insts.CoreOpsFunctionFnOnceTupleRangeUsizeU32
          (some { start := 17#usize, «end» := 19#usize }) b
      let i5 ← lift (core.option.Option.unwrap_or o5 0#u32)
      let o6 ←
        core.option.Option.map
          value.convert.parse_mysql_datetime_string.closure_3.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
          (some { start := 20#usize }) b
      let i6 ← lift (core.option.Option.unwrap_or o6 0#u32)
      ok (some (i, i1, i2, i3, i4, i5, i6))) ⦃ r => r.map dview = datetimeStringRead b.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, ds, ht, hd, ⟨h1, h2, h3⟩, hv⟩ := dsr_ns _ hR
  obtain ⟨d0, d1, d2, d3, d5, d6, d8, d9, d11, d12, d14, d15, d17, d18⟩ := hd
  have : 1 ≤ ds.length := by cases ds <;> simp_all
  apply WP.spec_mono (dt_block_spec b _ _ _ _ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: ds) (by simp [ht])
    ⟨d0, d1, d2, d3, d5, d6, d8, d9⟩
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d11, d12])
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d14, d15])
    (by rintro r ⟨⟩; simp [ht, Slice.length, List.slice, d17, d18])
    (by rintro st ⟨⟩; simp [ht, Slice.length, h1, h2, h3]))
  rintro r ⟨y, mo, d, h, mi, sec, us, rfl, e1, e2, e3, e4, e5, e6, e7⟩
  rw [hv]; simp [dview, e1, e2, e3, e4, e5, e6, e7, ht, List.slice]

private theorem dsr_some (t : List U8) (h : datetimeStringRead t ≠ none) :
    (t.length = 10 ∧ Trusted.Regex.asciiMatch .datetimeYmd t = true) ∨
    (t.length = 19 ∧ Trusted.Regex.asciiMatch .datetimeYmdHms t = true) ∨
    (20 < t.length ∧ t.length < 27 ∧ Trusted.Regex.asciiMatch .datetimeYmdHmsNs t = true) := by
  unfold datetimeStringRead at h
  match t with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: rest =>
    simp only at h
    split_ifs at h with hc
    · simp only [allDigits, List.all_cons, List.all_nil, isDigit, Bool.and_eq_true,
        decide_eq_true_eq, Bool.and_true, List.isEmpty_cons, Bool.not_false, Bool.true_and] at hc
      match rest with
      | [] =>
        left
        simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.matchSeq, Trusted.digit,
          Trusted.isAsciiDigit, Trusted.lit]
        omega
      | sp :: h1 :: h2 :: c1 :: mi1 :: mi2 :: c2 :: s1 :: s2 :: frac =>
        simp only at h
        split_ifs at h with hc2
        · simp only [allDigits, List.all_cons, List.all_nil, isDigit, Bool.and_eq_true,
            decide_eq_true_eq, Bool.and_true, List.isEmpty_cons, Bool.not_false, Bool.true_and] at hc2
          cases frac with
          | nil =>
            right; left
            simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, Trusted.matchSeq,
              Trusted.digit, Trusted.isAsciiDigit, Trusted.lit]
            omega
          | cons f ds =>
            right; right
            simp only [fracRead] at h
            split_ifs at h with hf
            · have hd : ∀ x ∈ ds, 48 ≤ x.val ∧ x.val ≤ 57 := by simpa [isDigit] using hf.2.2.2
              simp [Trusted.Regex.asciiMatch, Trusted.ymd, Trusted.ymdHms, Trusted.matchSeq,
                Trusted.digit, Trusted.isAsciiDigit, Trusted.lit, Trusted.matchFrac]
              and_intros
              all_goals omega
            · simp at h
        · simp at h
      | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
      | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] => simp at h
    · simp at h
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _] => simp at h

/-- `parse_mysql_datetime_string` (private, used by the chrono conversions): on ASCII input,
    total; the text `DATE`/`DATETIME` literal `datetimeStringRead`. **ASCII hypothesis:** on
    non-ASCII input the Unicode-mode regexes can match non-ASCII digits and the following
    `btou(..).unwrap()` panics (e.g. `"2020-01-01 00:00:00.\u{0660}"`); the regexes are only
    specified on ASCII input, so that case is excluded rather than stated. -/
theorem value.convert.parse_mysql_datetime_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_datetime_string b ⦃ r =>
      r.map (fun t => (t.1.val, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.1.val,
        t.2.2.2.2.2.1.val, t.2.2.2.2.2.2.val)) = datetimeStringRead b.val ⦄ := by
  have e1 : value.convert.trusted.datetime_re_ymd b = ok (Trusted.Regex.asciiMatch .datetimeYmd b.val) := by
    simp [value.convert.trusted.datetime_re_ymd, Trusted.isMatch_ascii _ _ ha]
  have e2 : value.convert.trusted.datetime_re_ymd_hms b = ok (Trusted.Regex.asciiMatch .datetimeYmdHms b.val) := by
    simp [value.convert.trusted.datetime_re_ymd_hms, Trusted.isMatch_ascii _ _ ha]
  have e3 : value.convert.trusted.datetime_re_ymd_hms_ns b = ok (Trusted.Regex.asciiMatch .datetimeYmdHmsNs b.val) := by
    simp [value.convert.trusted.datetime_re_ymd_hms_ns, Trusted.isMatch_ascii _ _ ha]
  have hl : (Slice.len b).val = b.val.length := by simp
  unfold value.convert.parse_mysql_datetime_string
  dsimp only
  simp only [e1, e2, e3, bind_ok]
  split_ifs
  all_goals try first
    | (have hlf := leaf_ymd b ‹_›; exact WP.spec_mono hlf (fun _ h => h))
    | (have hlf := leaf_ymdhms b ‹_›; exact WP.spec_mono hlf (fun _ h => h))
    | (have hlf := leaf_ns b ‹_›; exact WP.spec_mono hlf (fun _ h => h))
  all_goals
    simp only [WP.spec_ok, Option.map_none]
    symm; by_contra hne
    rcases dsr_some b.val hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  all_goals (simp only [UScalar.eq_equiv, UScalar.lt_equiv, hl] at *; simp_all)

end mysql_common
