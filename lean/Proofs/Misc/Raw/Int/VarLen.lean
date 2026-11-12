import Proofs.Util.IntAndMisc
import Proofs.Misc.Raw.Int.U8

/-! Statements for `impl IntRepr for VarLen` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

private def DInv (bs : List U8) (st : core.ops.range.Range Usize × io.ParseBuf × U64) : Prop :=
  st.1.start.val ≤ 5 ∧ st.1.end.val = 5 ∧ st.1.start.val ≤ bs.length ∧ st.2.1.val = bs.drop st.1.start.val ∧
    (∀ c ∈ bs.take st.1.start.val, 128 ≤ c.val) ∧ st.2.2.val = base128 (bs.take st.1.start.val)

private theorem deser_body (bs : List U8) (it : core.ops.range.Range Usize) (b : io.ParseBuf) (len : U64)
    (hinv : DInv bs (it, b, len)) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_loop.body it b len ⦃ r =>
      match r with
      | .done y => ((okPart y.1).map (·.val), y.2.val) = jsonbVarLenRead bs
      | .cont x' => DInv bs x' ∧ 5 - x'.1.start.val < 5 - it.start.val ⦄ := by
  obtain ⟨h5, hend, hlen, hb, hall, hl⟩ := hinv
  simp only at h5 hend hlen hb hall hl
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_loop.body
  step as ⟨ o, iter1, ho, hend1 ⟩
  by_cases hs : it.start.val < 5
  · have hc : it.start.val < it.end.val := by omega
    simp only [hc, ↓reduceIte] at ho
    obtain ⟨rfl, hst⟩ := ho
    simp only
    step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec as ⟨ r, buf1, hr ⟩
    by_cases hbl : 1 ≤ b.length
    · simp only [hbl, ↓reduceIte] at hr
      obtain ⟨hr1, hr2⟩ := hr
      obtain ⟨c, rest, hcb⟩ : ∃ c rest, b.val = c :: rest := by
        cases h : b.val with
        | nil => simp [Slice.length, h] at hbl
        | cons c rest => exact ⟨c, rest, rfl⟩
      rw [hcb] at hr1 hr2
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at hr1 hr2
      have hd : bs.drop it.start.val = c :: rest := by rw [← hb, hcb]
      have hlenlt : len.val < 128 ^ it.start.val := by
        rw [hl]; have := IntAndMisc.base128_lt (bs.take it.start.val); simpa [show (bs.take it.start.val).length = it.start.val by simp; omega] using this
      cases r with
      | Err e => simp [okPart] at hr1
      | Ok v0 =>
        simp only [okPart, Option.map_some, Option.some.injEq] at hr1
        simp [leNat] at hr1
        step*
        all_goals
          subst cf_post
          simp only [core.ops.control_flow.ControlFlow.Continue.injEq] at *
          obtain rfl : v0 = val := by assumption
          have hc256 : c.val < 256 := by scalar_tac
          have hbyte : byte.val = c.val := by
            rw [byte_post, UScalar.cast_val_eq, i1_post, hr1]; exact Nat.mod_eq_of_lt (by scalar_tac)
          have hi2 : i2.val = c.val % 128 := by
            rw [i2_post, UScalar.val_and, hbyte]; exact IntAndMisc.and127 _
          have hlen1 : len1.val = len.val + 128 ^ it.start.val * (c.val % 128) := by
            rw [len1_post, UScalar.val_or, i4_post, hi2, i3_post, show U64.size = 2 ^ 64 by rw [U64.size_def]; simp [U64.numBits]]
            exact IntAndMisc.varlen_or _ _ _ hs hlenlt
          have hi5v : i5.val = c.val &&& 128 := by rw [i5_post, UScalar.val_and, hbyte]; rfl
          have hi5 : (i5 = 0#u64) ↔ c.val < 128 := by
            rw [← IntAndMisc.and128 c.val hc256, ← hi5v]
            constructor
            · intro h; rw [h]; rfl
            · intro h; exact UScalar.eq_of_val_eq (by rw [h]; rfl)
        all_goals
          obtain ⟨ht, hdr, hil⟩ := IntAndMisc.take_succ_of_drop bs it.start.val c rest hd
        · have hi6 : i6.val = 2 ^ 32 - 1 := by
            rw [i6_post, UScalar.cast_val_eq]; rfl
          have hc : c.val < 128 := hi5.1 ‹i5 = 0#u64›
          have hgt : ¬ len1.val < 4294967296 := by
            have : len1 > i6 := ‹_›
            have := UScalar.lt_equiv i6 len1 |>.1 this
            omega
          rw [IntAndMisc.jsonbVarLenRead_some bs it.start.val hs hall c rest hd hc, ← hl, ← hlen1]
          simp [okPart, hgt, hr2]
        · have hi6 : i6.val = 2 ^ 32 - 1 := by
            rw [i6_post, UScalar.cast_val_eq]; rfl
          have hc : c.val < 128 := hi5.1 ‹i5 = 0#u64›
          have hle : len1.val < 4294967296 := by
            have : ¬ len1 > i6 := ‹_›
            have : ¬ i6.val < len1.val := fun h => this ((UScalar.lt_equiv i6 len1).2 h)
            omega
          rw [IntAndMisc.jsonbVarLenRead_some bs it.start.val hs hall c rest hd hc, ← hl, ← hlen1]
          have hi7 : i7.val = len1.val := by
            rw [i7_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simpa using hle)
          simp [okPart, hle, hr2, hi7]
        · have hc : ¬ c.val < 128 := fun h => ‹¬ i5 = 0#u64› (hi5.2 h)
          unfold DInv
          simp only
          refine ⟨⟨by omega, by rw [hend1]; exact hend, by omega, ?_, ?_, ?_⟩, by omega⟩
          · rw [hst, hdr, hr2]
          · rw [hst, ht]
            intro x hx
            simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hall x hx
            · omega
          · rw [hst, ht, IntAndMisc.base128_append, hlen1, hl]
            simp; left; omega
    · simp only [hbl, ↓reduceIte] at hr
      obtain ⟨hr1, rfl⟩ := hr
      cases r with
      | Ok v => simp [okPart] at hr1
      | Err e =>
        step*
        subst residual_post e_post r1_post
        have hnil : buf1.val = [] := by
          simp [Slice.length] at hbl; exact hbl
        rw [hnil] at hb
        have hbl' : bs.length ≤ it.start.val := by
          have := congrArg List.length hb; simp at this; omega
        rw [IntAndMisc.jsonbVarLenRead_none bs it.start.val hall (by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)])]
        simp [okPart, hnil, List.drop_eq_nil_of_le (by omega : bs.length ≤ 5)]
  · have hc : ¬ it.start.val < it.end.val := by omega
    simp only [hc, ↓reduceIte] at ho
    obtain ⟨rfl, hst⟩ := ho
    step*
    have h5' : it.start.val = 5 := by omega
    rw [h5'] at hb hall
    rw [IntAndMisc.jsonbVarLenRead_none bs 5 hall rfl]
    simp [okPart, hb]


private theorem put_u8_full (b : alloc.vec.Vec U8) (x : U8) (hb : ¬ b.length + 1 ≤ Usize.max) :
    ¬ alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 b x ⦃ _ => True ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice
    alloc.vec.Vec.extend_from_slice
  simp only [lift, Std.bind_ok]
  have hb' : ¬ (b.length + (Array.to_slice (Array.make 1#usize [x] (by simp))).length ≤ Usize.max) := by simpa using hb
  simp only [hb', ↓reduceDIte]
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
  exact PBUtil.not_spec_bind_left (put_u8_full b _ hb) hs

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
    · exact PBUtil.not_spec_bind_left (body_small_full v hv b hb)


/-- `VarLen::SIZE` is `None`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = none := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `VarLen::deserialize`: total; the JSONB varlen reader `jsonbVarLenRead` (at most 5 bytes,
    errors on more, on values above `u32::MAX`, and on end of input; the bytes read are consumed). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = jsonbVarLenRead buf.val ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_loop
  apply spec_bind (Pₘ := fun r => ((okPart r.1).map (·.val), r.2.val) = jsonbVarLenRead buf.val)
  · apply loop.spec_decr_nat (fun st => 5 - st.1.start.val) (DInv buf.val)
    · rintro ⟨it, b, len⟩ hinv
      simp only
      apply spec_mono (deser_body buf.val it b len hinv)
      intro r h
      cases r <;> exact h
    · refine ⟨by simp, ?_, by simp, by simp, by simp, by simp [base128]⟩
      simp [misc.raw.int.IntReprVarLenU32.deserialize.MAX_REPR_LEN]
  · rintro ⟨r, rest⟩ h
    simpa using h

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
    rw [byte1_post, PBUtil.byte_val, UScalar.val_or, hby]
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
  exact PBUtil.not_spec_bind_left (loop_small_fails _ x buf hx rfl)

end mysql_common
