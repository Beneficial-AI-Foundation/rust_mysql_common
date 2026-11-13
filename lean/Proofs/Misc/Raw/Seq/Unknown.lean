import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impl SeqRepr for Unknown` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem serialize_loop_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (it : core.slice.iter.Iter T)
    (hser : ∀ x ∈ it.slice.val, ∀ (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (buf : alloc.vec.Vec U8)
    (h : buf.length + ((it.slice.val.drop it.i).flatMap enc).length ≤ Usize.max) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_loop ser it buf ⦃ v => v.val = buf.val ++ (it.slice.val.drop it.i).flatMap enc ⦄ := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_loop
  apply loop.spec_decr_nat (fun p => p.1.slice.length - p.1.i)
    (fun p => p.1.slice = it.slice ∧ p.2.length + ((p.1.slice.val.drop p.1.i).flatMap enc).length ≤ Usize.max ∧
      p.2.val ++ (p.1.slice.val.drop p.1.i).flatMap enc = buf.val ++ (it.slice.val.drop it.i).flatMap enc)
  · rintro ⟨jt, b⟩ ⟨hs, hb1, hb2⟩
    simp only at hs hb1 hb2
    unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_loop.body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split_ifs with hlt
    · have hlt' : jt.i < jt.slice.val.length := by have := hlt; scalar_tac
      have hd : jt.slice.val.drop jt.i = jt.slice.val[jt.i] :: jt.slice.val.drop (jt.i + 1) :=
        List.drop_eq_getElem_cons hlt'
      rw [hd] at hb1 hb2
      simp only [List.flatMap_cons, List.length_append] at hb1 hb2
      step with hser jt.slice.val[jt.i] (by rw [← hs]; exact List.getElem_mem _) b (by scalar_tac) as ⟨ b1, hb ⟩
      refine ⟨hs, ?_, ?_, ?_⟩
      · have : b1.length = b.length + (enc (jt.slice.val)[jt.i]).length := by simp [hb]
        omega
      · rw [hb, ← hb2]; simp
      · have : jt.slice.length = jt.slice.val.length := rfl
        omega
    · have hlt' : jt.slice.val.length ≤ jt.i := by have := hlt; scalar_tac
      rw [← hb2, List.drop_of_length_le hlt']
      simp
  · exact ⟨rfl, h, rfl⟩

/-- `Unknown::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN_spec :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN.val = Usize.max := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN
  simp [core.num.Usize.MAX]

/-- `Unknown::SIZE` is `None`. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE_eq :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE = none := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE; rfl

/-- `Unknown::serialize`: appends the items' serializations, nothing else (the count is stored elsewhere). Stated given what the item serializer appends (`enc`) for the items of the sequence. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (seq : Slice T)
    (hser : ∀ x ∈ seq.val, ∀ (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (buf : alloc.vec.Vec U8)
    (h : buf.length + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize ser seq buf ⦃ buf' => buf'.val = buf.val ++ seq.val.flatMap enc ⦄ := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize
  simp only [core.slice.Slice.iter]
  step with serialize_loop_spec ser enc ⟨seq, 0⟩ hser buf (by simpa using h) as ⟨ v, hv ⟩
  simpa using hv

/-- `Unknown::deserialize(len)`: reads back `len` serialized items. Stated given that the item
    parser reads back each item's serialization `enc x`, and, if items have a fixed `SIZE`, that
    every `enc x` has that size and `SIZE * len` does not overflow (it is computed unchecked). -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (len : Usize) (hlen : len.val = xs.length) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = xs.flatMap enc ++ tail) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize
  rw [hsz]
  apply spec_bind_ok
  cases o with
  | none =>
    exact parse_items_roundtrip cl de enc xs hde len hlen buf tail h
  | some c =>
    obtain ⟨hc1, hc2⟩ := hfix c rfl
    have hfl := length_flatMap_const enc xs c hc1
    have hc3 : c.val * len.val ≤ Usize.max := by rw [hlen]; exact hc2
    step as ⟨ i, hi ⟩
    have hil : i.val ≤ buf.length := by simp [Slice.length, h, hi, hlen, hfl]
    step with parse_parsebuf_spec buf i as ⟨ r, buf1, hp ⟩
    simp only [hil, ↓reduceIte] at hp
    obtain ⟨hp1, hp2⟩ := hp
    cases r with
    | Err e => simp [okPart] at hp1
    | Ok pb =>
      simp [okPart] at hp1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      have hpb : pb.val = xs.flatMap enc ++ [] := by
        rw [hp1, h, List.append_nil, hi, hlen, ← hfl, List.take_left]
      apply spec_bind_ok
      dsimp only
      refine WP.spec_bind (parse_items_roundtrip cl de enc xs hde len hlen pb [] hpb) (fun q hq => ?_)
      obtain ⟨r1, rr⟩ := q
      obtain ⟨hq1, -⟩ := hq
      apply (WP.spec_ok _).mpr
      refine ⟨hq1, ?_⟩
      rw [hp2, h, hi, hlen, ← hfl, List.drop_left]

/-- `Unknown::deserialize(len)` does not panic if the item parser does not, provided
    `SIZE * len` does not overflow for a fixed-size item. **Caveats.** (1) `Vec::with_capacity(len)`
    is modelled as free: real Rust panics (capacity overflow) when `len * size_of::<T>()` exceeds
    `isize::MAX`, and aborts the process when the allocation fails (OOM). (2) The product `SIZE * len` is a plain `usize` multiplication: it panics on overflow
    in a debug build (as in the Lean model) and wraps in a release build. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (len : Usize) (hov : ∀ c, o = some c → c.val * len.val ≤ Usize.max) (buf : io.ParseBuf) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ _ => True ⦄ := by
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize
  rw [hsz]
  apply spec_bind_ok
  cases o with
  | none => exact parse_items_no_panic cl de hde len buf
  | some c =>
    have := hov c rfl
    step as ⟨ i, hi ⟩
    step with parse_parsebuf_spec buf i as ⟨ r, buf1, hp ⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pb =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      apply spec_bind_ok
      dsimp only
      step with parse_items_no_panic cl de hde len pb

end mysql_common
