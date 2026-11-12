import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for VarLen` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

private theorem put_u8_full (b : alloc.vec.Vec U8) (x : U8) (hb : ¬ b.length + 1 ≤ Usize.max) :
    ¬ alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 b x ⦃ _ => True ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice
    alloc.vec.Vec.extend_from_slice
  simp only [lift, Std.bind_ok]
  rw [dif_neg (by simpa using hb)]
  simp

private theorem body_small_full (v : U32) (hv : v.val < 128) (b : alloc.vec.Vec U8)
    (hb : ¬ b.length + 1 ≤ Usize.max) :
    ¬ misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop.body v b ⦃ _ => True ⦄ := by
  intro hs
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop.body at hs
  simp only [lift, Std.bind_ok] at hs
  obtain ⟨v1, hv1, hs⟩ := PBUtil.spec_eq_ok (IntAndMisc.spec_bind_inv hs)
  have h1 := U32.ShiftRight_IScalar_spec v 7#i32 (by decide) (by decide)
  rw [hv1, spec_ok] at h1
  have h0 : v1 = 0#u32 := by
    apply UScalar.eq_of_val_eq; rw [h1.1]; simp [Nat.shiftRight_eq_div_pow]; omega
  subst h0
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hs
  exact IntAndMisc.not_spec_bind (put_u8_full b _ hb) hs

private theorem body_small (v : U32) (hv : v.val < 128) (b : alloc.vec.Vec U8)
    (hb : b.length + 1 ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop.body v b ⦃ r => ∃ b', r = ControlFlow.cont (0#u32, b') ∧ b'.length = b.length + 1 ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop.body
  step*
  all_goals
    have h0 : val1 = 0#u32 := by
      apply UScalar.eq_of_val_eq; rw [val1_post]; simp [Nat.shiftRight_eq_div_pow]; omega
    subst h0
  all_goals first
    | (simp at *; done)
    | exact ⟨buf1, rfl, by simp [buf1_post]⟩

private theorem loop_small_fails : ∀ (n : Nat) (v : U32) (b : alloc.vec.Vec U8), v.val < 128 →
    Usize.max - b.length = n →
    ¬ misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop v b ⦃ _ => True ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v b hv hn
    unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop
    rw [loop]
    by_cases hb : b.length + 1 ≤ Usize.max
    · apply PBUtil.not_spec_bind (body_small v hv b hb)
      rintro r ⟨b', rfl, hb'⟩
      have := ih (Usize.max - b'.length) (by omega) 0#u32 b' (by decide) rfl
      unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop at this
      simpa using this
    · exact IntAndMisc.not_spec_bind (body_small_full v hv b hb)


/-- `VarLen::SIZE` is `None`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = none := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `VarLen::deserialize`: total; the JSONB varlen reader `jsonbVarLenRead` (at most 5 bytes,
    errors on more, on values above `u32::MAX`, and on end of input; the bytes read are consumed). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = jsonbVarLenRead buf.val ⦄ := by
  sorry

/-- `buf.parse::<RawInt<VarLen>>(())`: total; `jsonbVarLenRead` (`SIZE` is `None`, so this is `deserialize`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      ((okPart r).map (·.1.val), rest.val) = jsonbVarLenRead buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ buf () (by simp [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE, misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq])]
  have := IntAndMisc.rawint_deserialize_spec misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun o rest => (o.map (·.val), rest.val) = jsonbVarLenRead buf.val) (misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map, Function.comp_def] using h1

/-- `VarLen::deserialize` reads back the JSONB encoding `jsonbVarLen x` of every `u32`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = jsonbVarLen x.val ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf)
  rintro ⟨r, rest⟩ h1
  rw [h, IntAndMisc.jsonbVarLenRead_jsonbVarLen' _ _ x.hBounds] at h1
  simp only [Prod.mk.injEq] at h1
  refine ⟨?_, h1.2⟩
  obtain ⟨h1, -⟩ := h1
  cases hr : okPart r with
  | none => rw [hr] at h1; simp at h1
  | some y => rw [hr] at h1; simp at h1; rw [UScalar.eq_of_val_eq h1]

/-- **Bug.** `VarLen::serialize` does not write the JSONB encoding. Its loop has its two
    branches swapped (it stops, setting the continuation bit, as soon as more bits remain): for
    `x ≥ 128` it appends the single byte `(x mod 128) | 0x80` and drops the higher bits. Since
    that byte has its continuation bit set, `deserialize` goes on into whatever bytes follow it
    and can silently return a wrong value; at the end of the input it fails. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_large (x : U32) (buf : alloc.vec.Vec U8) (hx : 128 ≤ x.val)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [byte (x.val % 128 + 128)] ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop
  apply spec_bind (Pₘ := fun r : (alloc.vec.Vec U8 × U8) => r.1 = buf ∧ r.2.val = x.val % 128)
  · apply loop.spec_decr_nat (fun _ => 0) (fun st => st = (x, buf))
    · rintro ⟨v, b⟩ hst
      simp only [Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_loop.body
      step*
    · rfl
  · rintro ⟨b1, by1⟩ ⟨hb1, hby⟩
    simp only at hb1 hby
    subst hb1
    step*
    rw [buf'_post]; congr 2
    apply UScalar.eq_of_val_eq
    rw [byte1_post, IntAndMisc.byte_val', UScalar.val_or, hby]
    have hlt : x.val % 128 < 2 ^ 7 := by omega
    have := Nat.shiftLeft_add_eq_or_of_lt (a := 1) hlt
    simp only [Nat.one_shiftLeft] at this
    rw [show (128#u8).val = 2 ^ 7 from rfl, Nat.lor_comm, ← this]
    omega

/-- **Bug.** For `x < 128`, `VarLen::serialize` never returns: after writing `x` its loop keeps
    appending `0` bytes forever (in Rust: until allocation fails and the process aborts; in the
    Lean model: until the `Vec` reaches `usize::MAX` and the next `push` fails). It is stated as
    "does not return normally" rather than as an equation because the failure only comes after
    `usize::MAX` iterations of the loop. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_small_fails (x : U32) (buf : alloc.vec.Vec U8) (hx : x.val < 128) :
    ¬ misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize
  exact IntAndMisc.not_spec_bind (loop_small_fails _ x buf hx rfl)

end mysql_common
