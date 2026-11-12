import Defs
import Proofs.Util.ParseBuf
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.ParseBuf

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

theorem spec_bind_ok {α β : Type} {a : α} {k : α → Result β} {P : β → Prop} (h : k a ⦃ P ⦄) :
    (Std.bind (ok a) k) ⦃ P ⦄ :=
  WP.spec_bind ((WP.spec_ok _).mpr rfl) (fun x hx => hx ▸ h)

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

/-! ## `RawInt` wrapper -/

theorem rawint_new_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x = ok (x, ()) := rfl

theorem rawint_serialize_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) (u : core.marker.PhantomData T)
    (buf : alloc.vec.Vec U8) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst (x, u) buf = inst.serialize x buf := rfl

theorem rawint_parse_unchecked_spec {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf ()
      ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  unfold io.ParseBuf.parse_unchecked
  change misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst () buf ⦃ _ ⦄
  unfold misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok x =>
    simp only [misc.raw.int.RawInt.new]
    apply WP.spec_bind (Pₘ := fun (ri : misc.raw.int.RawInt T P) => ri.1 = x) ((WP.spec_ok _).mpr rfl)
    intro ri hri
    apply (WP.spec_ok _).mpr
    simpa [okPart, hri] using hr
  | Err e => simpa [okPart] using hr

/-! ## `put_u64_le` -/

theorem leNat_inj : ∀ (l1 l2 : List U8), l1.length = l2.length → leNat l1 = leNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | b1 :: l1, b2 :: l2, hl, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [leNat] at he
    have h1 : b1.val < 256 := by scalar_tac
    have h2 : b2.val < 256 := by scalar_tac
    have hv : b1.val = b2.val := by omega
    have hb : b1 = b2 := by scalar_tac
    rw [hb, leNat_inj l1 l2 hl (by omega)]

theorem toLEBytes_u64 (x : U64) :
    x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) = leBytes 8 x.val := by
  apply leNat_inj
  · simp [PBUtil.length_leBytes, BitVec.toLEBytes_length]
  · rw [PBUtil.leNat_leBytes, ← PBUtil.fromLEBytes_toNat, List.map_map]
    have : (U8.bv ∘ @UScalar.mk UScalarTy.U8) = id := by funext b; rfl
    rw [this, List.map_id, BitVec.fromLEBytes_toLEBytes (by decide)]
    simp only [BitVec.toNat_cast]
    have := x.hBounds
    rw [Nat.mod_eq_of_lt (by simpa using x.hBounds)]
    rfl

theorem put_u64_le_spec (buf : alloc.vec.Vec U8) (x : U64) (h : buf.length + 8 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le buf x ⦃ v => v.val = buf.val ++ leBytes 8 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le
  step as ⟨ a, ha ⟩
  step*
  simp_all
  exact toLEBytes_u64 x

/-! ## `parse_items` -/

theorem parse_items_loop_unfold {T : Type} (de : proto.MyDeserialize T Unit)
    (it : core.ops.range.Range Usize) (buf : io.ParseBuf) (seq : alloc.vec.Vec T) :
    misc.raw.seq.parse_items_loop de it buf seq =
      (do
        let r ← misc.raw.seq.parse_items_loop.body de it buf seq
        match r with
        | .cont (a, b, c) => misc.raw.seq.parse_items_loop de a b c
        | .done x => ok x) := by
  conv_lhs => unfold misc.raw.seq.parse_items_loop; rw [loop]
  congr 1
  funext r
  rcases r with ⟨a, b, c⟩ | x <;> rfl

theorem parse_items_loop_roundtrip {T : Type} (de : proto.MyDeserialize T Unit) (enc : T → List U8)
    (xs : List T)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (it : core.ops.range.Range Usize) (buf : io.ParseBuf) (seq : alloc.vec.Vec T) (tail : List U8)
    (hlen : it.end.val = it.start.val + xs.length) (hcap : seq.length + xs.length ≤ Usize.max)
    (hbuf : buf.val = xs.flatMap enc ++ tail) :
    misc.raw.seq.parse_items_loop de it buf seq ⦃ r rest =>
      (okPart r).map cowList = some (seq.val ++ xs) ∧ rest.val = tail ⦄ := by
  induction xs generalizing it buf seq with
  | nil =>
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    simp only [List.length_nil, Nat.add_zero] at hlen
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    rw [if_neg (by omega)] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp_all [okPart, cowList]
  | cons x xs ih =>
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    simp only [List.length_cons] at hlen
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    rw [if_pos (by omega)] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    step with hde x (by simp) (xs.flatMap enc ++ tail) buf (by simp [hbuf]) as ⟨ p, hr1, hr2 ⟩
    obtain ⟨r, buf1⟩ := p
    simp only at hr1 hr2 ⊢
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok v =>
      simp [okPart] at hr1
      subst hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with alloc.vec.Vec.push_spec seq v (by simp at hcap; scalar_tac) as ⟨ seq1, hseq1 ⟩
      have := ih (fun y hy => hde y (by simp [hy])) it1 buf1 seq1 (by rw [he, ho2]; omega)
        (by simp [hseq1] at *; scalar_tac) hr2
      apply WP.spec_mono this
      intro p hp
      simpa [hseq1] using hp

theorem parse_items_roundtrip {T : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (enc : T → List U8) (xs : List T)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (len : Usize) (hlen : len.val = xs.length) (buf : io.ParseBuf) (tail : List U8)
    (hbuf : buf.val = xs.flatMap enc ++ tail) :
    misc.raw.seq.parse_items cl de len buf (alloc.vec.Vec.with_capacity T len) ⦃ r rest =>
      (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  unfold misc.raw.seq.parse_items
  step with parse_items_loop_roundtrip de enc xs hde { start := 0#usize, «end» := len } buf
    (alloc.vec.Vec.with_capacity T len) tail (by simp [hlen])
    (by simp [alloc.vec.Vec.with_capacity]; scalar_tac) hbuf as ⟨ r, rest, h1, h2 ⟩
  simpa [alloc.vec.Vec.with_capacity] using And.intro h1 h2

theorem parse_items_loop_no_panic {T : Type} (de : proto.MyDeserialize T Unit)
    (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (it : core.ops.range.Range Usize) (buf : io.ParseBuf) (seq : alloc.vec.Vec T)
    (hcap : seq.length + (it.end.val - it.start.val) ≤ Usize.max) :
    misc.raw.seq.parse_items_loop de it buf seq ⦃ _ => True ⦄ := by
  unfold misc.raw.seq.parse_items_loop
  apply loop.spec_decr_nat (fun p => p.1.end.val - p.1.start.val)
    (fun p => p.2.2.length + (p.1.end.val - p.1.start.val) ≤ Usize.max)
  · rintro ⟨it, b, sq⟩ hinv
    simp only at hinv
    unfold misc.raw.seq.parse_items_loop.body
    step as ⟨ o, it1, ho, he ⟩
    split at ho
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1
      simp only
      have hp := hde b
      obtain ⟨⟨r, b1⟩, hrv, -⟩ := PBUtil.spec_eq_ok hp
      rw [hrv]; simp only [bind_ok]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok v =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch]
        step with alloc.vec.Vec.push_spec sq v (by scalar_tac) as ⟨ sq1, hsq1 ⟩
        refine ⟨?_, ?_⟩
        · simp [hsq1, he, ho2] at *; scalar_tac
        · rw [he, ho2]; omega
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1
      simp
  · exact hcap

theorem parse_items_no_panic {T : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄) (len : Usize) (buf : io.ParseBuf) :
    misc.raw.seq.parse_items cl de len buf (alloc.vec.Vec.with_capacity T len) ⦃ _ => True ⦄ := by
  unfold misc.raw.seq.parse_items
  step with parse_items_loop_no_panic de hde { start := 0#usize, «end» := len } buf
    (alloc.vec.Vec.with_capacity T len) (by simp [alloc.vec.Vec.with_capacity]; scalar_tac)

theorem length_flatMap_const {T : Type} (enc : T → List U8) (xs : List T) (c : Nat)
    (h : ∀ x ∈ xs, (enc x).length = c) : (xs.flatMap enc).length = c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    ring

/-- Parsing a `ParseBuf` of `n` bytes (as in `SeqRepr::deserialize` for fixed-size items). -/
theorem parse_parsebuf_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.parse io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf n ⦃ r rest =>
      if n.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])]
  exact io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec n buf

theorem length_flatMap_take_le {T : Type} (enc : T → List U8) (l : List T) (n : Nat) :
    ((l.take n).flatMap enc).length ≤ (l.flatMap enc).length := by
  have : l.flatMap enc = (l.take n).flatMap enc ++ (l.drop n).flatMap enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [this, List.length_append]; omega

end mysql_common
