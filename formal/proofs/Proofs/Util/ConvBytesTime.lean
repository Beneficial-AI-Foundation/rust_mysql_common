import Defs

/-! Helper lemmas for the stage g proofs of the byte/string/duration conversions
(`Proofs/Value/Convert/{FromBytes,String,VecU8,CowSliceU8,ArrayU8N,Duration,FromDuration,
MysqlTimeToDuration,ParseMysqlTimeString,ParseMysqlDatetimeString}.lean`,
`Proofs/Defs/LemmasG.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.CBTUtil

/-! ## UTF-8: `utf8`, `Trusted.bytesOf` and Lean's `String` -/

theorem uint8_byte (b : UInt8) : UInt8.ofNat (byte b.toNat).val = b := by
  simp only [byte]
  apply UInt8.toNat_inj.mp
  simp [UScalar.val]

theorem byte_val (x : U8) : byte x.val = x := by
  rcases x with ⟨bv⟩
  simp only [byte, UScalar.val]
  congr 1
  rw [BitVec.ofNat_toNat]; exact BitVec.setWidth_eq bv

theorem bytesOf_utf8 (s : String) : Trusted.bytesOf (utf8 s) = s.toByteArray := by
  simp [Trusted.bytesOf, utf8, List.map_map, Function.comp_def, uint8_byte]

theorem utf8_ofByteArray (bs : List U8) (h : (Trusted.bytesOf bs).IsValidUTF8) :
    utf8 (String.ofByteArray _ h) = bs := by
  simp [Trusted.bytesOf, utf8, List.map_map, Function.comp_def, byte_val]

theorem utf8_inj {s t : String} (h : utf8 s = utf8 t) : s = t := by
  have := congrArg Trusted.bytesOf h
  rw [bytesOf_utf8, bytesOf_utf8] at this
  exact String.toByteArray_inj.mp this

theorem fromUTF8?_bytesOf_some {bs : List U8} {s : String}
    (h : String.fromUTF8? (Trusted.bytesOf bs) = some s) : utf8 s = bs := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; exact utf8_ofByteArray _ _
  · cases h

theorem fromUTF8?_bytesOf_none {bs : List U8}
    (h : String.fromUTF8? (Trusted.bytesOf bs) = none) (s : String) : utf8 s ≠ bs := by
  intro hs
  unfold String.fromUTF8? at h
  split at h
  · cases h
  · rename_i hv; apply hv; rw [← hs, bytesOf_utf8]; exact s.isValidUTF8

theorem fromUTF8?_utf8 (s : String) : String.fromUTF8? (Trusted.bytesOf (utf8 s)) = some s := by
  cases h : String.fromUTF8? (Trusted.bytesOf (utf8 s)) with
  | none => exact absurd rfl (fromUTF8?_bytesOf_none h s)
  | some t => rw [utf8_inj (fromUTF8?_bytesOf_some h)]

theorem u8sOf_toUTF8 (s : String) : Trusted.u8sOf s.toUTF8 = utf8 s := by
  simp only [Trusted.u8sOf, utf8]
  congr 1
  funext b
  rcases b with ⟨bv⟩
  simp [byte, UInt8.toNat]

/-! ## `from_value_opt` of a `FromValue` whose intermediate is the type itself -/

/-- The default `from_value_opt` with `Into = FromSame` keeps any postcondition of `try_from`. -/
theorem from_value_opt_same_spec {T : Type} (m : Result (core.result.Result T value.convert.FromValueError))
    (P : core.result.Result T value.convert.FromValueError → Prop) (h : m ⦃ r => P r ⦄) :
    (do
      let r ← m
      match r with
      | core.result.Result.Ok x => do
        let t ← core.convert.IntoFrom.into (core.convert.FromSame T) x
        ok (core.result.Result.Ok t)
      | core.result.Result.Err e => ok (core.result.Result.Err e)) ⦃ r => P r ⦄ := by
  apply WP.spec_bind h
  rintro (x|e) hr <;> simpa [core.convert.IntoFrom.into, core.convert.FromSame.from] using hr

theorem vec_deref_val {T : Type} (b : alloc.vec.Vec T) : (alloc.vec.Vec.deref b).val = b.val := by
  simp [alloc.vec.Vec.deref, Slice.from_val]

/-- A computation with a (total-correctness) spec returns `ok`. -/
theorem spec_exists_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) :
    ∃ r, m = ok r ∧ P r := by
  cases m <;> simp_all

/-! ## Step lemmas for `lift` -/

@[step]
theorem lift_spec {α : Type} (x : α) : lift x ⦃ y => y = x ⦄ := by simp [lift]

/-- An unsigned multiplication that overflows fails with `integerOverflow`. -/
theorem umul_overflow {ty : UScalarTy} (x y : UScalar ty) (h : 2 ^ ty.numBits ≤ x.val * y.val) :
    x * y = fail .integerOverflow := by
  show UScalar.mul x y = _
  simp only [UScalar.mul, UScalar.tryMk]
  have := UScalar.tryMkOpt_eq ty (x.val * y.val)
  cases hc : UScalar.tryMkOpt ty (x.val * y.val) with
  | none => rfl
  | some z => rw [hc] at this; exfalso; simp [UScalar.inBounds] at this; omega

/-! ## Durations -/

/-- `Duration::new(secs, nanos)` when the carried seconds fit in a `u64`. -/
@[step]
theorem duration_new_spec (secs : U64) (nanos : U32) (h : secs.val + nanos.val / 1000000000 ≤ U64.max) :
    value.convert.trusted.duration_new secs nanos ⦃ d => durNanos d = secs.val * 10 ^ 9 + nanos.val ⦄ := by
  unfold value.convert.trusted.duration_new
  split
  · simp [durNanos]
  · have hm := UScalar.tryMkOpt_eq .U64 (secs.val + nanos.val / 1000000000)
    split
    · rename_i s hs
      rw [hs] at hm
      simp only [WP.spec_ok, durNanos, UScalar.ofNatCore_val_eq, hm.1]
      omega
    · rename_i hs
      rw [hs] at hm
      exfalso; apply hm
      simp only [UScalar.inBounds, UScalarTy.numBits]
      simp [U64.max, U64.numBits, UScalarTy.numBits] at h ⊢; omega

/-! ## Splitting seconds into days, hours, minutes and seconds -/

theorem split_a1 (S : Nat) : (S - S % 60) % 3600 / 60 = S % 3600 / 60 := by omega
theorem split_a2 (S : Nat) : S - S % 60 - S % 3600 / 60 * 60 = S - S % 3600 := by omega
theorem split_a3 (S : Nat) : (S - S % 3600) % 86400 / 3600 = S % 86400 / 3600 := by omega
theorem split_a4 (S : Nat) : S - S % 3600 - S % 86400 / 3600 * 3600 = S - S % 86400 := by omega
theorem split_a5 (S : Nat) : (S - S % 86400) / 86400 = S / 86400 := by omega
theorem split_join (S : Nat) :
    ((S / 86400 % 2 ^ 32 * 24 + S % 86400 / 3600) * 60 + S % 3600 / 60) * 60 + S % 60 =
      S % (86400 * 2 ^ 32) := by
  norm_num; omega

/-! ## Text literals: bounds -/

theorem digitsVal_lt (ds : List U8) (h : ds.all isDigit) : digitsVal ds < 10 ^ ds.length := by
  have key : ∀ (acc : Nat) (ds : List U8), ds.all isDigit →
      ds.foldl (fun acc d => 10 * acc + (d.val - 48)) acc < (acc + 1) * 10 ^ ds.length := by
    intro acc ds
    induction ds generalizing acc with
    | nil => simp
    | cons d ds ih =>
      intro hd
      simp only [List.all_cons, Bool.and_eq_true, isDigit, decide_eq_true_eq] at hd
      simp only [List.foldl_cons, List.length_cons]
      have := ih (10 * acc + (d.val - 48)) hd.2
      calc _ < _ := this
        _ ≤ (acc + 1) * 10 ^ (ds.length + 1) := by
          rw [pow_succ]
          have : 10 * acc + (d.val - 48) + 1 ≤ (acc + 1) * 10 := by omega
          calc (10 * acc + (d.val - 48) + 1) * 10 ^ ds.length
              ≤ ((acc + 1) * 10) * 10 ^ ds.length := Nat.mul_le_mul_right _ this
            _ = _ := by ring
  have := key 0 ds h
  simpa [digitsVal] using this

theorem fracRead_lt {l : List U8} {us : Nat} (h : fracRead l = some us) : us < 10 ^ 6 := by
  cases l with
  | nil => simp [fracRead] at h; omega
  | cons c ds =>
    simp only [fracRead] at h
    split at h
    · rename_i hc
      cases h
      have h1 := digitsVal_lt ds hc.2.2.2
      have : 10 ^ ds.length * 10 ^ (6 - ds.length) = 10 ^ 6 := by
        rw [← pow_add]; congr 1; omega
      calc digitsVal ds * 10 ^ (6 - ds.length) < 10 ^ ds.length * 10 ^ (6 - ds.length) :=
            Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ = _ := this
    · cases h

theorem timeStringRead_us_lt {bs : List U8} {n : Bool} {h m s us : Nat}
    (hr : timeStringRead bs = some (n, h, m, s, us)) : us < 10 ^ 6 := by
  unfold timeStringRead at hr
  generalize (match bs with
    | c :: rest => if c.val = 45 then (true, rest) else (false, bs)
    | [] => (false, [])) = p at hr
  obtain ⟨neg, t⟩ := p
  simp only at hr
  generalize (match t with
    | h1 :: h2 :: h3 :: rest =>
      if digitUpTo 8 h1 ∧ isDigit h2 ∧ isDigit h3 then some (digitsVal [h1, h2, h3], rest)
      else if isDigit h1 ∧ isDigit h2 then some (digitsVal [h1, h2], h3 :: rest)
      else none
    | _ => none) = hours at hr
  split at hr
  · split at hr
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨u, hu, he⟩ := hr
      rw [← he.2.2.2.2]; exact fracRead_lt hu
    · cases hr
  · cases hr

/-! ## `btou` -/

theorem isAsciiDigit_eq : Trusted.isAsciiDigit = isDigit := rfl

theorem decimalDigits_eq (l : List U8) (h1 : l ≠ []) (h2 : l.all isDigit) :
    Trusted.decimalDigits? l = some (digitsVal l) := by
  simp [Trusted.decimalDigits?, isAsciiDigit_eq, h2, h1, digitsVal]

theorem btou_spec' (ty : UScalarTy) (s : Slice U8) (h1 : s.val ≠ []) (h2 : s.val.all isDigit)
    (hb : digitsVal s.val < 2 ^ ty.numBits) :
    ∃ x, Trusted.btou ty s = some x ∧ x.val = digitsVal s.val := by
  simp only [Trusted.btou, decimalDigits_eq _ h1 h2, Option.bind_some]
  have := UScalar.tryMkOpt_eq ty (digitsVal s.val)
  cases hc : UScalar.tryMkOpt ty (digitsVal s.val) with
  | none => rw [hc] at this; exfalso; apply this; simpa [UScalar.inBounds] using hb
  | some x => rw [hc] at this; exact ⟨x, rfl, this.1⟩

@[step]
theorem btou_u32_spec (s : Slice U8) (h1 : s.val ≠ []) (h2 : s.val.all isDigit)
    (h3 : s.val.length ≤ 9) :
    value.convert.trusted.btou_u32 s ⦃ o => ∃ x, o = some x ∧ x.val = digitsVal s.val ⦄ := by
  have hb : digitsVal s.val < 2 ^ UScalarTy.U32.numBits := by
    have := digitsVal_lt s.val h2
    have : 10 ^ s.val.length ≤ 10 ^ 9 := Nat.pow_le_pow_right (by norm_num) h3
    simp [UScalarTy.numBits]; omega
  obtain ⟨x, hx, hv⟩ := btou_spec' .U32 s h1 h2 hb
  simp [value.convert.trusted.btou_u32, hx, hv]

@[step]
theorem btou_u8_spec (s : Slice U8) (h1 : s.val ≠ []) (h2 : s.val.all isDigit)
    (h3 : s.val.length ≤ 2) :
    value.convert.trusted.btou_u8 s ⦃ o => ∃ x, o = some x ∧ x.val = digitsVal s.val ⦄ := by
  have hb : digitsVal s.val < 2 ^ UScalarTy.U8.numBits := by
    have := digitsVal_lt s.val h2
    have : 10 ^ s.val.length ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) h3
    simp [UScalarTy.numBits]; omega
  obtain ⟨x, hx, hv⟩ := btou_spec' .U8 s h1 h2 hb
  simp [value.convert.trusted.btou_u8, hx, hv]

/-! ## `parse_micros` -/

@[step]
theorem parse_micros_loop0_spec (s : Slice U8) (p : Usize) (hp : p.val ≤ s.length) :
    value.convert.parse_micros_loop0 s p ⦃ q => q.val ≤ s.length ⦄ := by
  unfold value.convert.parse_micros_loop0
  apply loop.spec_decr_nat (fun p : Usize => s.length - p.val) (fun p : Usize => p.val ≤ s.length)
  · intro p hp
    unfold value.convert.parse_micros_loop0.body
    step*
  · exact hp

@[step]
theorem parse_micros_loop1_spec (it : core.ops.range.Range Usize) (m : U32)
    (hle : it.start.val ≤ it.end.val) (hb : m.val * 10 ^ (it.end.val - it.start.val) < 2 ^ 32) :
    value.convert.parse_micros_loop1 it m ⦃ r => r.val = m.val * 10 ^ (it.end.val - it.start.val) ⦄ := by
  unfold value.convert.parse_micros_loop1
  apply loop.spec_decr_nat (fun x : core.ops.range.Range Usize × U32 => x.1.end.val - x.1.start.val)
    (fun x => x.1.start.val ≤ x.1.end.val ∧ x.1.end = it.end ∧
      x.2.val * 10 ^ (x.1.end.val - x.1.start.val) = m.val * 10 ^ (it.end.val - it.start.val))
  · rintro ⟨it', m'⟩ ⟨h1, h2, h3⟩
    unfold value.convert.parse_micros_loop1.body
    simp only at h1 h2 h3
    step*
    · split at o_post
      · simp_all
      · have hk : it'.end.val - it'.start.val = 0 := by omega
        rw [hk] at h3; simpa using h3
    · split at o_post
      · have hk : 1 ≤ it'.end.val - it'.start.val := by omega
        have : 10 ≤ 10 ^ (it'.end.val - it'.start.val) := by
          calc 10 = 10 ^ 1 := by norm_num
            _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hk
        have : m'.val * 10 ≤ m'.val * 10 ^ (it'.end.val - it'.start.val) := Nat.mul_le_mul_left _ this
        have hlt2 : m'.val * 10 ^ (it'.end.val - it'.start.val) < 2 ^ 32 := h3 ▸ hb
        have e10 : (10#u32).val = 10 := rfl
        rw [e10]
        scalar_tac
      · simp_all
    · split at o_post
      · obtain ⟨_, hs⟩ := o_post
        have hk : it'.end.val - it'.start.val = (iter1.end.val - iter1.start.val) + 1 := by
          rw [o_post1]; omega
        refine ⟨by rw [o_post1]; omega, by rw [o_post1, h2], ?_, by rw [o_post1]; omega⟩
        rw [← h3, hk, micros1_post, pow_succ]; ring
      · simp_all
  · exact ⟨hle, rfl, rfl⟩

@[step]
theorem parse_micros_spec (s : Slice U8) (h1 : s.val ≠ []) (h2 : s.val.all isDigit)
    (h3 : s.val.length ≤ 6) :
    value.convert.parse_micros s ⦃ r => r.val = digitsVal s.val * 10 ^ (6 - s.val.length) ⦄ := by
  unfold value.convert.parse_micros
  have hd := digitsVal_lt s.val h2
  step*
  have hm : micros.val = digitsVal s.val := by
    simp_all
  have hl : s.len.val = s.val.length := by simp [Slice.len]
  have hi3 : i3.val = 6 - s.val.length := by
    rw [i3_post, i_post, i2_post, hl]; simp [Slice.length] at pad_zero_cnt_post; omega
  simp only [hi3, hm]
  have : 10 ^ s.val.length * 10 ^ (6 - s.val.length) = 10 ^ 6 := by rw [← pow_add]; congr 1; omega
  have := Nat.mul_lt_mul_of_pos_right hd (show 0 < 10 ^ (6 - s.val.length) by positivity)
  simp only [UScalar.ofNatCore_val_eq, Nat.sub_zero] at *
  omega

/-! ## `parse_mysql_time_string`: the fraction closure and the field-reading blocks -/

/-- The microseconds of the fraction digits `ds` (`.ds`). -/
def fracVal (ds : List U8) : Nat := digitsVal ds * 10 ^ (6 - ds.length)

@[step]
theorem time_micros_map_spec (M : Option (core.ops.range.RangeFrom Usize)) (b : Slice U8)
    (h : ∀ st : core.ops.range.RangeFrom Usize, M = some st → st.start.val ≤ b.length ∧
      b.val.drop st.start.val ≠ [] ∧ (b.val.drop st.start.val).all isDigit ∧
      (b.val.drop st.start.val).length ≤ 6) :
    core.option.Option.map
      value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32
      M b ⦃ o => o.map (·.val) = M.map (fun st => fracVal (b.val.drop st.start.val)) ⦄ := by
  cases M with
  | none => simp
  | some st =>
    obtain ⟨h1, h2, h3, h4⟩ := h st rfl
    simp only [core.option.Option.map,
      value.convert.parse_mysql_time_string.closure.Insts.CoreOpsFunctionFnOnceTupleRangeFromUsizeU32.call_once]
    apply WP.spec_bind (Pₘ := fun v : U32 => v.val = fracVal (b.val.drop st.start.val))
    · step*
      simp_all [fracVal]
    · intro v hv; simp [hv]

end mysql_common.CBTUtil
