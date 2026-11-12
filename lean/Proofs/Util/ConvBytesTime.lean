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

end mysql_common.CBTUtil
