import Defs

/-! Helper lemmas for the proofs of `Proofs/Misc/Raw/Bytes/*` and `Proofs/Misc/Raw/Seq/*`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ## Monadic plumbing -/

/-- A computation whose bind satisfies a spec satisfies `True`: used for the `_panics` lemmas. -/
theorem spec_of_bind {α β : Type} (m : Result α) (k : α → Result β) (P : β → Prop)
    (h : (Std.bind m k) ⦃ P ⦄) : m ⦃ fun _ => True ⦄ := by
  revert h
  refine Result.cases (motive := fun m => (Std.bind m k) ⦃ P ⦄ → m ⦃ fun _ => True ⦄) m ?_ ?_ ?_
  · intro r _; simp
  · intro i k' h; simp at h
  · intro h; simp at h

/-! ## `usize` bounds -/

theorem usize_lt_of_le_max {n : Nat} (h : n ≤ Usize.max) : n < 2 ^ UScalarTy.Usize.numBits := by
  have h1 := Usize.max_def; rw [Usize.numBits_def] at h1
  have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  omega

theorem lt_two_pow_64_of_le_max {n : Nat} (h : n ≤ Usize.max) : n < 2 ^ 64 := by
  have h1 := Usize.max_def; rw [Usize.numBits_def] at h1
  have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have h3 : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ 64 := by
    apply Nat.pow_le_pow_right (by omega)
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  omega

/-! ## Small std/crate functions -/

@[step]
theorem cow_as_ref_spec {T : Type} (cl : core.clone.Clone T) (c : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) :
    alloc.borrow.Cow.Insts.CoreConvertAsRef.as_ref (Slice.Insts.AllocBorrowToOwnedVec cl) c ⦃ s => s.val = cowList c ⦄ := by
  cases c <;> simp [alloc.borrow.Cow.Insts.CoreConvertAsRef.as_ref, alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref,
    cowList, alloc.vec.Vec.Insts.CoreBorrowBorrowSlice.borrow, alloc.vec.Vec.deref]

@[step]
theorem cow_deref_spec {T : Type} (cl : core.clone.Clone T) (c : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) :
    alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref (Slice.Insts.AllocBorrowToOwnedVec cl) c ⦃ s => s.val = cowList c ⦄ := by
  cases c <;> simp [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref,
    cowList, alloc.vec.Vec.Insts.CoreBorrowBorrowSlice.borrow, alloc.vec.Vec.deref]

@[step]
theorem min_usize_spec (a b : Usize) : core.cmp.min core.cmp.OrdUsize a b ⦃ c => c.val = min a.val b.val ⦄ := by
  simp [core.cmp.impls.OrdUsize.min]
  split <;> omega

@[step]
theorem put_slice_spec (buf : alloc.vec.Vec U8) (s : Slice U8) (h : buf.length + s.length ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice buf s ⦃ v => v.val = buf.val ++ s.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp [h]
  step as ⟨ s', hs' ⟩
  all_goals simp_all

@[step]
theorem put_u8_spec (buf : alloc.vec.Vec U8) (x : U8) (h : buf.length + 1 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 buf x ⦃ v => v.val = buf.val ++ [x] ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8
  step*

/-! ## `beforeZero` -/

@[simp] theorem beforeZero_nil : beforeZero [] = [] := rfl

theorem beforeZero_cons (b : U8) (l : List U8) :
    beforeZero (b :: l) = if b.val = 0 then [] else b :: beforeZero l := by
  unfold beforeZero
  by_cases hb : b.val = 0 <;> simp [hb]

theorem beforeZero_length_le (l : List U8) : (beforeZero l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => by_cases hb : b.val = 0 <;> simp [beforeZero_cons, hb, ih]

theorem take_beforeZero_length (l : List U8) : l.take (beforeZero l).length = beforeZero l := by
  induction l with
  | nil => simp
  | cons b l ih => by_cases hb : b.val = 0 <;> simp [beforeZero_cons, hb, ih]

theorem beforeZero_eq_self (l : List U8) (h : ¬ ∃ b ∈ l, b.val = 0) : beforeZero l = l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.mem_cons, exists_eq_or_imp, not_or] at h
    simp [beforeZero_cons, h.1, ih h.2]

theorem beforeZero_length_lt (l : List U8) (h : ∃ b ∈ l, b.val = 0) :
    (beforeZero l).length < l.length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b.val = 0
    · simp [beforeZero_cons, hb]
    · have h' : ∃ b ∈ l, b.val = 0 := by
        obtain ⟨c, hc, hc0⟩ := h
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact absurd hc0 hb
        · exact ⟨c, hc, hc0⟩
      have := ih h'
      simp [beforeZero_cons, hb]; omega

theorem beforeZero_append_zero (s t : List U8) (hs : ∀ b ∈ s, b.val ≠ 0) :
    beforeZero (s ++ byte 0 :: t) = s := by
  induction s with
  | nil => simp [beforeZero_cons, byte]; rfl
  | cons b s ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hs
    simp [beforeZero_cons, hs.1, ih hs.2]

/-! ## `position_of_zero` -/

theorem beforeZero_length_of (l : List U8) (i : Nat) (hi : i < l.length)
    (h1 : ∀ b ∈ l.take i, b.val ≠ 0) (h2 : (l[i]'hi).val = 0) :
    (beforeZero l).length = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    cases i with
    | zero => simp_all [beforeZero]
    | succ i =>
      simp only [List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at h1
      have := ih i (by simp at hi; omega) h1.2 h2
      simp_all [beforeZero]

theorem position_of_zero_loop_spec (s : Slice U8) (i : Usize) (hi : i.val ≤ s.length)
    (h : ∀ b ∈ s.val.take i.val, b.val ≠ 0) :
    io.position_of_zero_loop s i ⦃ o =>
      if ∃ b ∈ s.val, b.val = 0 then o.map (·.val) = some (beforeZero s.val).length else o = none ⦄ := by
  unfold io.position_of_zero_loop
  apply loop.spec_decr_nat (fun i => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ b ∈ s.val.take i.val, b.val ≠ 0)
  · intro i ⟨hi, h⟩
    unfold io.position_of_zero_loop.body
    step*
    · have hlt : i.val < s.val.length := by scalar_tac
      have hz : (s.val[i.val]'hlt).val = 0 := by subst i2_post; simp_all
      split
      · simp [beforeZero_length_of s.val i.val hlt h hz]
      · rename_i hc; exact absurd ⟨_, List.getElem_mem hlt, hz⟩ hc
    · have hlt : i.val < s.val.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i3_post, List.take_add_one, List.getElem?_eq_getElem hlt]
      intro b hb
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact h b hb
      · subst hb; intro h0; apply ‹¬i2 = 0#u8›; subst i2_post; scalar_tac
    · have hge : s.val.length ≤ i.val := by scalar_tac
      rw [List.take_of_length_le hge] at h
      split
      · rename_i hc; obtain ⟨b, hb, hb0⟩ := hc; exact absurd hb0 (h b hb)
      · trivial
  · exact ⟨hi, h⟩

@[step]
theorem position_of_zero_spec (s : Slice U8) :
    io.position_of_zero s ⦃ o =>
      if ∃ b ∈ s.val, b.val = 0 then o.map (·.val) = some (beforeZero s.val).length else o = none ⦄ :=
  position_of_zero_loop_spec s 0#usize (by simp) (by simp)

/-! ## Array equality -/

theorem allM_zip_eq (l1 l2 : List U8) (h : l1.length = l2.length) :
    List.allM (fun (x : U8 × U8) => ok (decide (x.1.val = x.2.val))) (List.zip l1 l2) = ok (decide (l1 = l2)) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all; rfl
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp at h
      by_cases hab : a = b
      · subst hab; simp [ih l2 h]
      · have : a.val ≠ b.val := fun e => hab (by scalar_tac)
        simp [this, hab]; rfl

@[step]
theorem array_u8_eq_spec {N : Usize} (a0 a1 : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a0 a1 ⦃ b => b = true ↔ a0.val = a1.val ⦄ := by
  unfold core.array.equality.PartialEqArray.eq
  simp
  rw [allM_zip_eq _ _ (by simp)]
  simp

end mysql_common
