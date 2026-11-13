import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Seq.Unknown

/-! Statements for `impl SeqRepr for LeU32` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem serialize_loop_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (tk : core.iter.adapters.take.Take (core.slice.iter.Iter T))
    (hser : ∀ x ∈ (tk.iter.slice.val.drop tk.iter.i).take tk.n.val, ∀ (b : alloc.vec.Vec U8),
      b.length + (enc x).length ≤ Usize.max → ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (buf : alloc.vec.Vec U8)
    (h : buf.length + (((tk.iter.slice.val.drop tk.iter.i).take tk.n.val).flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_loop ser tk buf ⦃ v => v.val = buf.val ++ ((tk.iter.slice.val.drop tk.iter.i).take tk.n.val).flatMap enc ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_loop
  apply loop.spec_decr_nat (fun p => p.1.n.val)
    (fun p => p.2.length + (((p.1.iter.slice.val.drop p.1.iter.i).take p.1.n.val).flatMap enc).length ≤ Usize.max ∧
      p.2.val ++ ((p.1.iter.slice.val.drop p.1.iter.i).take p.1.n.val).flatMap enc =
        buf.val ++ ((tk.iter.slice.val.drop tk.iter.i).take tk.n.val).flatMap enc ∧
      ∀ x ∈ (p.1.iter.slice.val.drop p.1.iter.i).take p.1.n.val,
        x ∈ (tk.iter.slice.val.drop tk.iter.i).take tk.n.val)
  · rintro ⟨jt, b⟩ ⟨hb1, hb2, hb3⟩
    simp only at hb1 hb2 hb3
    unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_loop.body
    simp only [core.iter.adapters.take.IteratorTake.next]
    split_ifs with hn
    · rw [hn] at hb2
      apply spec_bind_ok
      apply (WP.spec_ok _).mpr
      rw [← hb2]; simp
    · step as ⟨ n', hn' ⟩
      simp only [core.slice.iter.IteratorSliceIter.next]
      split_ifs with hlt
      · have hlt' : jt.iter.i < jt.iter.slice.val.length := by have := hlt; scalar_tac
        have hd : (jt.iter.slice.val.drop jt.iter.i).take jt.n.val =
            jt.iter.slice.val[jt.iter.i] :: (jt.iter.slice.val.drop (jt.iter.i + 1)).take n'.val := by
          rw [List.drop_eq_getElem_cons hlt', hn']
          obtain ⟨k, hk⟩ : ∃ k, jt.n.val = k + 1 := ⟨jt.n.val - 1, by omega⟩
          rw [hk, List.take_succ_cons]; simp
        rw [hd] at hb1 hb2 hb3
        simp only [List.flatMap_cons, List.length_append] at hb1 hb2
        apply spec_bind_ok
        apply spec_bind_ok
        step with hser jt.iter.slice.val[jt.iter.i] (hb3 _ (List.mem_cons_self ..)) b (by scalar_tac) as ⟨ b1, hb ⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · have : b1.length = b.length + (enc (jt.iter.slice.val)[jt.iter.i]).length := by simp [hb]
          omega
        · rw [hb, ← hb2]; simp
        · intro x hx; exact hb3 x (List.mem_cons_of_mem _ hx)
        · omega
      · have hlt' : jt.iter.slice.val.length ≤ jt.iter.i := by have := hlt; scalar_tac
        apply spec_bind_ok
        apply spec_bind_ok
        apply (WP.spec_ok _).mpr
        rw [← hb2, List.drop_of_length_le hlt']
        simp
  · exact ⟨h, rfl, fun x hx => hx⟩

/-- `LeU32::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN
  simp only [WP.spec_ok, UScalar.cast_val_eq, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> simp [core.num.U32.MAX, U32.rMax]

/-- `LeU32::SIZE` is `None`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE = none := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE; rfl

/-- `LeU32::serialize`: appends the item count (at most `MAX_LEN`) as a 4-byte little-endian integer, then the serializations of the first that many items: a longer sequence is silently truncated. Stated given what the item serializer appends (`enc`) for the items written. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (seq : Slice T)
    (hser : ∀ x ∈ seq.val.take (2 ^ 32 - 1), ∀ (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + ((seq.val.take (2 ^ 32 - 1)).flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize ser seq buf ⦃ buf' =>
      buf'.val = buf.val ++ leBytes 4 (min seq.length (2 ^ 32 - 1)) ++ (seq.val.take (2 ^ 32 - 1)).flatMap enc ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize
  have hm : misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN = ok (UScalar.cast .Usize core.num.U32.MAX) := by unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN; rfl
  rw [hm]
  apply spec_bind_ok
  step as ⟨ len, hlen ⟩
  have hmv : (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = min (2 ^ 32 - 1) Usize.max := by
    simp only [UScalar.cast_val_eq, UScalarTy.Usize_numBits_eq]
    have h1 := Usize.max_def; rw [Usize.numBits_def, UScalarTy.Usize_numBits_eq] at h1
    rw [h1]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> simp [core.num.U32.MAX, U32.rMax]
  have hseq : seq.length ≤ Usize.max := by scalar_tac
  have hlen' : len.val = min seq.length (2 ^ 32 - 1) := by rw [hlen, hmv]; scalar_tac
  step as ⟨ i2, hi2 ⟩
  have hi2' : i2.val = min seq.length (2 ^ 32 - 1) := by
    rw [hi2, UScalar.cast_val_mod_pow_of_inBounds_eq]
    · exact hlen'
    · have := lt_two_pow_64_of_le_max (show len.val ≤ Usize.max by scalar_tac)
      simp; omega
  have hfl : seq.val.take len.val = seq.val.take (2 ^ 32 - 1) := by
    rw [List.take_eq_take_iff, hlen']; simp only [Slice.length]; omega
  rw [← hfl] at h
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec i2 buf (by scalar_tac) as ⟨ buf1, hb1 ⟩
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.take.trait_default,
    core.iter.traits.iterator.Iterator.take.default]
  apply spec_bind_ok
  apply spec_bind_ok
  step with serialize_loop_spec ser enc ⟨⟨seq, 0⟩, len⟩ (by
    intro x hx; simp only [List.drop_zero] at hx; rw [hfl] at hx; exact hser x hx) buf1 (by
    have : buf1.length = buf.length + 4 := by simp [hb1]
    simp only [List.drop_zero]; omega) as ⟨ v, hv ⟩
  simp only [List.drop_zero] at hv
  rw [hv, hb1, hi2', hlen']
  simp only [List.append_assoc]
  congr 2
  have hsl : seq.length = seq.val.length := rfl
  rcases Nat.le_total seq.val.length (2 ^ 32 - 1) with hh | hh
  · rw [hsl, Nat.min_eq_left hh, List.take_of_length_le (le_refl _), List.take_of_length_le hh]
  · rw [hsl, Nat.min_eq_right hh]

/-- `LeU32::deserialize`: reads back a 4-byte count followed by that many serialized items (hypotheses as for `Unknown`). -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (hlen : xs.length ≤ (2 ^ 32 - 1)) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 xs.length ++ xs.flatMap enc ++ tail) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
  have hxl : xs.length < 2 ^ 32 := by omega
  have hl : (leBytes 4 xs.length).length = 4 := PBUtil.length_leBytes 4 xs.length
  have hn : leNat (leBytes 4 xs.length) = xs.length := by
    rw [PBUtil.leNat_leBytes]; exact Nat.mod_eq_of_lt (by simpa using hxl)
  have hK : 4 ≤ buf.length := by simp [Slice.length, h, hl]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  simp only [hK, ↓reduceIte] at hr
  obtain ⟨hr1, hr2⟩ := hr
  cases r with
  | Err e => simp [okPart] at hr1
  | Ok val =>
    simp [okPart] at hr1
    rw [h, List.append_assoc, List.take_left' hl, hn] at hr1
    rw [h, List.append_assoc, List.drop_left' hl] at hr2
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    apply spec_bind_ok
    obtain ⟨v, _⟩ := val
    simp only at hr1
    simp only [misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref]
    apply spec_bind_ok
    step as ⟨ len, hcl ⟩
    have hlen' : len.val = xs.length := by
      rw [hcl, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by rw [hr1]; exact usize_lt_of_le_max (by have h1 := Usize.max_def; rw [Usize.numBits_def] at h1; have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by omega) (by rcases System.Platform.numBits_eq with h | h <;> simp [h]); omega))]
      exact hr1
    exact misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_roundtrip cl de xs enc hde o hsz hfix len hlen' tail buf1 hr2

/-- `LeU32::deserialize` does not panic if the item parser does not, provided `SIZE * count`
    does not overflow, where `count` is the length prefix read from the (untrusted) input.
    **Crash path.** The count comes from the wire, up to `u32::MAX`. For a fixed-size item the
    unchecked product `SIZE * count` overflows for a large count (a panic in a debug build, a
    wrap-around in release); and before that, `Vec::with_capacity(count)` (modelled as free) asks
    for `count * size_of::<T>()` bytes: Rust panics (capacity overflow) if that exceeds
    `isize::MAX` and aborts the process if the allocation fails (OOM). Both are reachable from a
    malicious server. (On a 32-bit `usize` the count is truncated by `as usize`; `hov` bounds the
    untruncated count, so no `Target64` is needed.) -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o) (buf : io.ParseBuf)
    (hov : ∀ c, o = some c → c.val * leNat (buf.val.take 4) ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok val =>
    split at hr
    · obtain ⟨hr1, hr2⟩ := hr
      simp [okPart] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      apply spec_bind_ok
      obtain ⟨v, _⟩ := val
      simp only at hr1
      simp only [misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref]
      apply spec_bind_ok
      step as ⟨ len, hcl ⟩
      have hle : len.val ≤ leNat (buf.val.take 4) := by
        rw [hcl, UScalar.cast_val_eq, ← hr1]; exact Nat.mod_le _ _
      exact misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_no_panic cl de hde o hsz len
        (fun c hc => le_trans (Nat.mul_le_mul_left _ hle) (hov c hc)) buf1
    · simp [okPart] at hr

end mysql_common
