import Defs
import Proofs.Util.CompCodec
import Proofs.Defs.LemmasComp

/-! Statements for `fn compress_with` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

/-! Helper specs of the `compress_with` loop. -/

namespace mysql_common.CompCodec

open WP

@[step]
theorem u24_le_bytes_spec (n : Usize) : proto.codec.u24_le_bytes n ⦃ a => a.val = leBytes 3 n.val ⦄ := by
  unfold proto.codec.u24_le_bytes
  step*
  · rcases System.Platform.numBits_eq with h | h <;> simp [h]
  · rcases System.Platform.numBits_eq with h | h <;> simp [h]
  · simp only [Array.make_val, leBytes, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩
    all_goals
      apply UScalar.eq_of_val_eq
      simp only [i_post, i2_post, i4_post, UScalar.cast_val_eq, i1_post, i3_post, PBUtil.byte_val,
        Nat.shiftRight_eq_div_pow]
    all_goals simp
    all_goals omega

theorem chunksOf_drop_mul (n : Nat) (hn : 0 < n) (bs : List U8) (k : Nat) :
    (chunksOf n bs).drop k = chunksOf n (bs.drop (k * n)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← List.drop_drop, ih]
    by_cases hb : bs.drop (k * n) = []
    · rw [hb, chunksOf_nil]
      have : bs.drop ((k + 1) * n) = [] := by
        rw [Nat.succ_mul, ← List.drop_drop, hb]; simp
      rw [this, chunksOf_nil]; simp
    · rw [chunksOf_cons n hn _ hb]
      simp [List.drop_drop, Nat.succ_mul]

theorem chunksOf_getElem? (n : Nat) (hn : 0 < n) (bs : List U8) (k : Nat) (hk : k * n < bs.length) :
    (chunksOf n bs)[k]? = some ((bs.drop (k * n)).take n) := by
  have : (chunksOf n bs)[k]? = ((chunksOf n bs).drop k)[0]? := by simp
  rw [this, chunksOf_drop_mul n hn, chunksOf_cons n hn _ (by simp; omega)]
  simp

theorem lt_length_chunksOf (n : Nat) (hn : 0 < n) (bs : List U8) (k : Nat) :
    k < (chunksOf n bs).length ↔ k * n < bs.length := by
  have h1 : k < (chunksOf n bs).length ↔ (chunksOf n bs).drop k ≠ [] := by simp
  rw [h1, chunksOf_drop_mul n hn]
  constructor
  · intro h; by_contra hc
    rw [List.drop_eq_nil_of_le (by omega), chunksOf_nil] at h; exact h rfl
  · intro h; rw [chunksOf_cons n hn _ (by simp; omega)]; simp

theorem compPackets_append (seq : Nat) (cs : List (List U8)) (zs : List (Option (List U8)))
    (h : cs.length = zs.length) (c : List U8) (z : Option (List U8)) :
    compPackets seq (cs ++ [c]) (zs ++ [z]) = compPackets seq cs zs ++ compPacket (seq + cs.length) c z := by
  induction cs generalizing seq zs with
  | nil =>
    cases zs with
    | nil => simp [compPackets]
    | cons _ _ => simp at h
  | cons c' cs ih =>
    cases zs with
    | nil => simp at h
    | cons z' zs =>
      simp only [List.cons_append, compPackets, List.length_cons]
      rw [ih (seq + 1) zs (by simpa using h)]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem deflateReach_snoc (a b : flate2.mem.Compress) (c : Slice U8) (h : DeflateReach a b) :
    DeflateReach a (Trusted.deflateState b c) := by
  induction h with
  | refl d => exact .step _ _ c (.refl _)
  | step d d' c' _ ih => exact .step _ _ c' ih

open proto.codec.buf_model

/-- The loop invariant of `compress_with`: `k` pieces done. -/
def CWInv (lvl : flate2.Compression) (dinit : Option flate2.mem.Compress) (n : Nat) (seq0 : U8) (plain dst0 : List U8)
    (x : U8 × Option flate2.mem.Compress × VecBuf × Usize) : Prop :=
  ∃ k out, x.2.2.2.val = min (k * n) plain.length ∧ k ≤ (chunksOf n plain).length ∧
    x.1 = byte (seq0.val + k) ∧
    CompPacketsOf (dinit.getD (Trusted.compressNew lvl)) lvl.level.val seq0.val ((chunksOf n plain).take k) out ∧
    x.2.2.1.val = dst0 ++ out ∧ out.length ≤ 8 * x.2.2.2.val ∧
    (match x.2.1 with
     | none => dinit = none
     | some d => DeflateReach (dinit.getD (Trusted.compressNew lvl)) d)

/-- The result of `compress_with` on a non-empty `src` (as `compress_with_spec`). -/
def CWPost (lvl : flate2.Compression) (dinit : Option flate2.mem.Compress) (n : Nat) (seq0 : U8) (src : VecBuf) (dst0 : List U8)
    (y : core.result.Result U8 proto.codec.error.PacketCodecError × Option flate2.mem.Compress × VecBuf × VecBuf) : Prop :=
  match y.1 with
  | .Ok s =>
    s = byte (seq0.val + (chunksOf n src.val).length) ∧ y.2.2.1.val = [] ∧
    ∃ out, CompEncoding (dinit.getD (Trusted.compressNew lvl)) lvl.level.val n seq0.val src.val out ∧ y.2.2.2.val = dst0 ++ out
  | .Err e =>
    (∃ ioe, e = .Io ioe) ∧ y.2.2.1 = src ∧
    ∃ k out, k < (chunksOf n src.val).length ∧ lvl.level.val ≠ 0 ∧
      minCompressLength ≤ ((chunksOf n src.val).getD k []).length ∧
      CompPacketsOf (dinit.getD (Trusted.compressNew lvl)) lvl.level.val seq0.val ((chunksOf n src.val).take k) out ∧
      y.2.2.2.val = dst0 ++ out

theorem cpo_snoc (d0 : flate2.mem.Compress) (lv seq0 : Nat) (cs : List (List U8)) (k : Nat) (out : List U8)
    (h : CompPacketsOf d0 lv seq0 (cs.take k) out) (c : List U8) (hc : cs[k]? = some c) (zo : Option (List U8))
    (he : EncChoice d0 lv c zo) :
    CompPacketsOf d0 lv seq0 (cs.take (k + 1)) (out ++ compPacket (seq0 + k) c zo) := by
  obtain ⟨zs, hF, rfl⟩ := h
  have hkl : k < cs.length := by
    by_contra hh; rw [List.getElem?_eq_none (by omega)] at hc; cases hc
  have ht : cs.take (k + 1) = cs.take k ++ [c] := by
    rw [List.take_add_one, hc]; rfl
  have hlen : (cs.take k).length = zs.length := hF.length_eq
  refine ⟨zs ++ [zo], ?_, ?_⟩
  · rw [ht]; exact List.rel_append hF (List.Forall₂.cons he .nil)
  · rw [ht, compPackets_append _ _ _ hlen]
    simp [List.length_take, Nat.min_eq_left (le_of_lt hkl)]

theorem wrap_one (x : U8) : core.num.U8.wrapping_add x 1#u8 = byte (x.val + 1) := by
  simp only [core.num.U8.wrapping_add, UScalar.wrapping_add, byte]
  congr 1

theorem byte_succ (a k : Nat) : byte ((byte (a + k)).val + 1) = byte (a + (k + 1)) := by
  apply UScalar.eq_of_val_eq; simp only [PBUtil.byte_val]; omega

theorem cw_next (lvl : flate2.Compression) (dinit : Option flate2.mem.Compress) (n : Nat) (hn : 0 < n) (seq0 : U8)
    (plain dst0 : List U8) (k : Nat) (out : List U8) (start : Nat)
    (hstart : start = min (k * n) plain.length)
    (hout : CompPacketsOf (dinit.getD (Trusted.compressNew lvl)) lvl.level.val seq0.val ((chunksOf n plain).take k) out)
    (hol : out.length ≤ 8 * start) (hlt : start < plain.length)
    (zo : Option (List U8)) (henc : EncChoice (dinit.getD (Trusted.compressNew lvl)) lvl.level.val ((plain.drop start).take n) zo)
    (seq' : U8) (hseq' : seq' = byte (seq0.val + (k + 1)))
    (dst' : VecBuf) (hd' : dst'.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((plain.drop start).take n) zo))
    (i3 : Usize) (hi3 : i3.val = start + min n (plain.length - start)) (defl' : Option flate2.mem.Compress)
    (hdefl' : match defl' with
     | none => dinit = none
     | some d => DeflateReach (dinit.getD (Trusted.compressNew lvl)) d) :
    CWInv lvl dinit n seq0 plain dst0 (seq', defl', dst', i3) ∧ plain.length - i3.val < plain.length - start := by
  have hkn : start = k * n := by omega
  have hk : k < (chunksOf n plain).length := (lt_length_chunksOf n hn plain k).mpr (by omega)
  have hc := chunksOf_getElem? n hn plain k (by omega)
  rw [← hkn] at hc
  have hcl := (compPacket_length lvl.level.val (seq0.val + k) _ zo henc.1).1
  have hcn : ((plain.drop start).take n).length = min n (plain.length - start) := by simp
  refine ⟨⟨k + 1, _, ?_, by omega, hseq', cpo_snoc _ _ _ _ _ _ hout _ hc zo henc, hd', ?_, hdefl'⟩, by omega⟩
  · simp only [hi3]; rw [Nat.succ_mul]
    omega
  · simp only [List.length_append, hi3]; omega

theorem cw_body_spec (lvl : flate2.Compression) (dinit : Option flate2.mem.Compress) (src : VecBuf) (n : Usize)
    (hn : 0 < n.val) (seq0 : U8) (dst0 : List U8)
    (hlvl : dinit ≠ none ∨ lvl.level.val ≤ 10 ∨ Nat.min n.val src.val.length < minCompressLength)
    (h : dst0.length + 8 * src.val.length ≤ Usize.max)
    (x : U8 × Option flate2.mem.Compress × VecBuf × Usize) (hx : CWInv lvl dinit n.val seq0 src.val dst0 x) :
    proto.codec.compress_with_loop.body VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear
      VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve
      lvl src n x.1 x.2.1 x.2.2.1 x.2.2.2 ⦃ r =>
      match r with
      | .done y => CWPost lvl dinit n.val seq0 src dst0 y
      | .cont x' => CWInv lvl dinit n.val seq0 src.val dst0 x' ∧
          src.val.length - x'.2.2.2.val < src.val.length - x.2.2.2.val ⦄ := by
  obtain ⟨seq, defl, dst, start⟩ := x
  obtain ⟨k, out, hstart, hk, hseq, hout, hdst, hol, hdefl⟩ := hx
  simp only at hstart hseq hdst hol hdefl ⊢
  unfold proto.codec.compress_with_loop.body
  simp only [proto.codec.trusted.compression_none, proto.codec.trusted.compression_eq, constants.MIN_COMPRESS_LENGTH,
    core.cmp.min]
  step*
  all_goals try (
    have hlt : start.val < src.val.length := by
      have := ‹start < s.len›; simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, s_post] at this; exact this
    have hcm : (core.cmp.impls.OrdUsize.min n i2).val = min n.val (src.val.length - start.val) := by
      simp only [core.cmp.impls.OrdUsize.min_val, i2_post, Slice.len_val, Slice.length, s_post]
    have hch : chunk.val = (src.val.drop start.val).take n.val := by
      rw [chunk_post, List.slice, i3_post, hcm, s_post, Nat.add_sub_cancel_left, List.take_eq_take_iff]
      simp
    have hchl : chunk.val.length = min n.val (src.val.length - start.val) := by rw [hch]; simp
    have hdl : dst.val.length ≤ dst0.length + 8 * start.val := by rw [hdst]; simp; omega
    have hsl : start.val + min n.val (src.val.length - start.val) ≤ src.val.length := by omega
    have hcpos : 0 < min n.val (src.val.length - start.val) := by omega
    clear chunk_post i2_post)
  · -- bound
    simp_all [Array.to_slice, PBUtil.length_leBytes]; omega
  · -- bound
    simp_all [Array.to_slice, PBUtil.length_leBytes]; omega
  · -- level 0: stored
    have hbytes : dst5.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) none) := by
      rw [dst5_post, dst4_post, dst3_post, dst2_post, dst1_post, hdst, s1_post, s2_post, s3_post, ← hch]
      simp [Array.to_slice, a_post, compPacket, compHeader, hseq, leBytes]
      rfl
    exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt none
      ⟨trivial, fun _ => Or.inl (by simpa using ‹(lvl.level.val == (0#u32).val) = true›)⟩ seq_id1 (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst5 hbytes i3
      (by rw [i3_post, hcm]) defl hdefl
  · -- a new deflate stream
    have hdn : dinit = none := by rw [‹defl = none›] at hdefl; exact hdefl
    have hl10 : ¬ lvl.level.val > 10 := by
      rcases hlvl with h1 | h1 | h1
      · exact absurd hdn h1
      · omega
      · have h5 := ‹chunk.len ≥ 512#usize›
        rw [ge_iff_le, UScalar.le_equiv] at h5
        have : chunk.len.val = min n.val (src.val.length - start.val) := by rw [Slice.len_val]; exact hchl
        have h1' : min n.val src.val.length < 512 := h1
        have : (512#usize).val = 512 := by simp
        omega
    simp only [proto.codec.trusted.compress_new, hl10, ↓reduceIte, Std.bind_ok]
    have HDR0 : DeflateReach (dinit.getD (Trusted.compressNew lvl)) (Trusted.compressNew lvl) := by
      rw [hdn]; exact .refl _
    have hbig : 512 ≤ chunk.val.length := by
      have h5 := ‹chunk.len ≥ 512#usize›
      rw [ge_iff_le, UScalar.le_equiv] at h5; simpa using h5
    have hbig' : minCompressLength ≤ ((src.val.drop start.val).take n.val).length := by
      rw [← hch, show minCompressLength = 512 from rfl]; exact hbig
    have hl0 : lvl.level.val ≠ 0 := by
      have := ‹¬(lvl.level.val == (0#u32).val) = true›; simpa using this
    have hkn : start.val = k * n.val := by omega
    have hkl : k < (chunksOf n.val src.val).length := (lt_length_chunksOf n.val hn src.val k).mpr (by omega)
    have hgd : (chunksOf n.val src.val).getD k [] = (src.val.drop start.val).take n.val := by
      rw [List.getD_eq_getElem?_getD, hkn, chunksOf_getElem? n.val hn src.val k (by omega)]; rfl
    simp only [proto.codec.trusted.deflate, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hdlen : dst.val.length + 8 * chunk.val.length ≤ Usize.max := by rw [hchl]; omega
    cases hR : Trusted.deflateResult (Trusted.compressNew lvl) chunk with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from]
      exact ⟨⟨e, rfl⟩, rfl, k, out, hkl, hl0, by rw [hgd]; exact hbig', hout, by rw [dst1_post, hdst]⟩
    | Ok val =>
      cases val with
      | none =>
        step with u24_le_bytes_spec as ⟨a, ha⟩
        step as ⟨s1, hs1⟩
        step with vb_put_slice_spec dst1 s1 (by simp [hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d3, hd3⟩
        step as ⟨s2, hs2⟩
        step with vb_put_slice_spec d3 s2 (by simp [hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d4, hd4⟩
        step as ⟨s3, hs3⟩
        step with vb_put_slice_spec d4 s3 (by simp [hs3, hd4, hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d5, hd5⟩
        step with vb_put_slice_spec d5 chunk (by simp [hd5, hs3, hd4, hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨dst2, hdst2⟩
        step as ⟨seq_id1, seq_id1_post⟩
        have hbytes : dst2.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) none) := by
          rw [hdst2, hd5, hd4, hd3, dst1_post, hdst, hs1, hs2, hs3, ← hch]
          simp [Array.to_slice, ha, compPacket, compHeader, hseq, leBytes]
          rfl
        exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt none
          ⟨trivial, fun _ => Or.inr (Or.inr ⟨(Trusted.compressNew lvl), chunk, HDR0, hch, hR⟩)⟩ seq_id1
          (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst2 hbytes i3
          (by rw [i3_post, hcm]) _ (deflateReach_snoc _ _ chunk HDR0)
      | some z =>
        have hzs := Trusted.deflateResult_short (Trusted.compressNew lvl) chunk z hR
        step with u24_le_bytes_spec as ⟨a, ha⟩
        step as ⟨s1, hs1⟩
        step with vb_put_slice_spec dst1 s1 (by simp [hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d3, hd3⟩
        step as ⟨s2, hs2⟩
        step with vb_put_slice_spec d3 s2 (by simp [hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d4, hd4⟩
        step with u24_le_bytes_spec as ⟨a1, ha1⟩
        step as ⟨s3, hs3⟩
        step with vb_put_slice_spec d4 s3 (by simp [hs3, hd4, hs2, hd3, hs1, ha1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d5, hd5⟩
        step with vb_put_slice_spec d5 (alloc.vec.Vec.deref z) (by simp [hd5, hs3, hd4, hs2, hd3, hs1, ha1, alloc.vec.Vec.deref, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨dst2, hdst2⟩
        step as ⟨seq_id1, seq_id1_post⟩
        have hbytes : dst2.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) (some z.val)) := by
          rw [hdst2, hd5, hd4, hd3, dst1_post, hdst, hs1, hs2, hs3, ← hch]
          simp [Array.to_slice, ha, ha1, compPacket, compHeader, hseq, alloc.vec.Vec.deref]
        exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt (some z.val)
          ⟨⟨hl0, hbig', (Trusted.compressNew lvl), chunk, z, hch, rfl, hR⟩, fun h => by cases h⟩ seq_id1
          (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst2 hbytes i3
          (by rw [i3_post, hcm]) _ (deflateReach_snoc _ _ chunk HDR0)
  · -- the kept deflate stream
    have HDR1 : DeflateReach (dinit.getD (Trusted.compressNew lvl)) new_deflater := by
      rw [‹defl = some new_deflater›] at hdefl; exact hdefl
    have hbig : 512 ≤ chunk.val.length := by
      have h5 := ‹chunk.len ≥ 512#usize›
      rw [ge_iff_le, UScalar.le_equiv] at h5; simpa using h5
    have hbig' : minCompressLength ≤ ((src.val.drop start.val).take n.val).length := by
      rw [← hch, show minCompressLength = 512 from rfl]; exact hbig
    have hl0 : lvl.level.val ≠ 0 := by
      have := ‹¬(lvl.level.val == (0#u32).val) = true›; simpa using this
    have hkn : start.val = k * n.val := by omega
    have hkl : k < (chunksOf n.val src.val).length := (lt_length_chunksOf n.val hn src.val k).mpr (by omega)
    have hgd : (chunksOf n.val src.val).getD k [] = (src.val.drop start.val).take n.val := by
      rw [List.getD_eq_getElem?_getD, hkn, chunksOf_getElem? n.val hn src.val k (by omega)]; rfl
    simp only [proto.codec.trusted.deflate, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hdlen : dst.val.length + 8 * chunk.val.length ≤ Usize.max := by rw [hchl]; omega
    cases hR : Trusted.deflateResult new_deflater chunk with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from]
      exact ⟨⟨e, rfl⟩, rfl, k, out, hkl, hl0, by rw [hgd]; exact hbig', hout, by rw [dst1_post, hdst]⟩
    | Ok val =>
      cases val with
      | none =>
        step with u24_le_bytes_spec as ⟨a, ha⟩
        step as ⟨s1, hs1⟩
        step with vb_put_slice_spec dst1 s1 (by simp [hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d3, hd3⟩
        step as ⟨s2, hs2⟩
        step with vb_put_slice_spec d3 s2 (by simp [hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d4, hd4⟩
        step as ⟨s3, hs3⟩
        step with vb_put_slice_spec d4 s3 (by simp [hs3, hd4, hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d5, hd5⟩
        step with vb_put_slice_spec d5 chunk (by simp [hd5, hs3, hd4, hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨dst2, hdst2⟩
        step as ⟨seq_id1, seq_id1_post⟩
        have hbytes : dst2.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) none) := by
          rw [hdst2, hd5, hd4, hd3, dst1_post, hdst, hs1, hs2, hs3, ← hch]
          simp [Array.to_slice, ha, compPacket, compHeader, hseq, leBytes]
          rfl
        exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt none
          ⟨trivial, fun _ => Or.inr (Or.inr ⟨new_deflater, chunk, HDR1, hch, hR⟩)⟩ seq_id1
          (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst2 hbytes i3
          (by rw [i3_post, hcm]) _ (deflateReach_snoc _ _ chunk HDR1)
      | some z =>
        have hzs := Trusted.deflateResult_short new_deflater chunk z hR
        step with u24_le_bytes_spec as ⟨a, ha⟩
        step as ⟨s1, hs1⟩
        step with vb_put_slice_spec dst1 s1 (by simp [hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d3, hd3⟩
        step as ⟨s2, hs2⟩
        step with vb_put_slice_spec d3 s2 (by simp [hs2, hd3, hs1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d4, hd4⟩
        step with u24_le_bytes_spec as ⟨a1, ha1⟩
        step as ⟨s3, hs3⟩
        step with vb_put_slice_spec d4 s3 (by simp [hs3, hd4, hs2, hd3, hs1, ha1, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨d5, hd5⟩
        step with vb_put_slice_spec d5 (alloc.vec.Vec.deref z) (by simp [hd5, hs3, hd4, hs2, hd3, hs1, ha1, alloc.vec.Vec.deref, Array.to_slice, ha, PBUtil.length_leBytes, dst1_post]; omega) as ⟨dst2, hdst2⟩
        step as ⟨seq_id1, seq_id1_post⟩
        have hbytes : dst2.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) (some z.val)) := by
          rw [hdst2, hd5, hd4, hd3, dst1_post, hdst, hs1, hs2, hs3, ← hch]
          simp [Array.to_slice, ha, ha1, compPacket, compHeader, hseq, alloc.vec.Vec.deref]
        exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt (some z.val)
          ⟨⟨hl0, hbig', new_deflater, chunk, z, hch, rfl, hR⟩, fun h => by cases h⟩ seq_id1
          (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst2 hbytes i3
          (by rw [i3_post, hcm]) _ (deflateReach_snoc _ _ chunk HDR1)
  · -- bound
    simp_all [Array.to_slice, PBUtil.length_leBytes]; omega
  · -- bound
    simp_all [Array.to_slice, PBUtil.length_leBytes]; omega
  · -- short piece: stored
    have hbytes : dst5.val = dst0 ++ (out ++ compPacket (seq0.val + k) ((src.val.drop start.val).take n.val) none) := by
      rw [dst5_post, dst4_post, dst3_post, dst2_post, dst1_post, hdst, s1_post, s2_post, s3_post, ← hch]
      simp [Array.to_slice, a_post, compPacket, compHeader, hseq, leBytes]
      rfl
    exact cw_next lvl dinit n.val hn seq0 src.val dst0 k out start.val hstart hout hol hlt none
      ⟨trivial, fun _ => Or.inr (Or.inl (by
        have h5 := ‹¬ chunk.len ≥ 512#usize›
        have h6 : chunk.len.val < 512 := by
          rw [ge_iff_le, UScalar.le_equiv, not_le] at h5; simpa using h5
        rw [Slice.len_val] at h6
        rw [← hch, show minCompressLength = 512 from rfl]; exact h6))⟩ seq_id1 (by rw [seq_id1_post, wrap_one, hseq, byte_succ]) dst5 hbytes i3
      (by rw [i3_post, hcm]) defl hdefl
  · -- the end of the input
    have hge : src.val.length ≤ start.val := by
      have := ‹¬ start < s.len›; simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, s_post] at this; omega
    have hkn : src.val.length ≤ k * n.val := by omega
    have hkl : k = (chunksOf n.val src.val).length := by
      have := (lt_length_chunksOf n.val hn src.val k).not.mpr (by omega); omega
    subst hkl
    rw [List.take_of_length_le (le_refl _)] at hout
    exact ⟨hseq, src1_post, out, hout, hdst⟩

theorem cw_loop_spec (lvl : flate2.Compression) (dinit : Option flate2.mem.Compress) (src : VecBuf) (n : Usize)
    (hn : 0 < n.val) (seq0 : U8) (dst0 : VecBuf)
    (hlvl : dinit ≠ none ∨ lvl.level.val ≤ 10 ∨ Nat.min n.val src.val.length < minCompressLength)
    (h : dst0.val.length + 8 * src.val.length ≤ Usize.max) :
    proto.codec.compress_with_loop VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear
      VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve
      seq0 lvl dinit src dst0 n 0#usize ⦃ y => CWPost lvl dinit n.val seq0 src dst0.val y ⦄ := by
  unfold proto.codec.compress_with_loop
  apply loop.spec_decr_nat (fun x => src.val.length - x.2.2.2.val) (CWInv lvl dinit n.val seq0 src.val dst0.val)
  · intro x hx
    apply spec_mono (cw_body_spec lvl dinit src n hn seq0 dst0.val hlvl h x hx)
    intro r hr; cases r <;> exact hr
  · refine ⟨0, [], by simp, by simp, ?_, ⟨[], .nil, rfl⟩, by simp, by simp, ?_⟩
    · apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; have := seq0.hBounds; simp at this ⊢
    · cases dinit with
      | none => rfl
      | some d => exact .refl _

end mysql_common.CompCodec

namespace mysql_common

open CompCodec WP

/-- `compress_with(.., deflater, ..)` on an empty `src`: `Ok(0)`, nothing changed (the same quirk as `compress`). -/
theorem proto.codec.compress_with_empty (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d max src dst = ok (.Ok 0#u8, d, src, dst) := by
  unfold proto.codec.compress_with
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  simp [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    alloc.vec.Vec.deref, hsrc]

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). `compress_with` with `max_allowed_packet = 0` on a non-empty `src` panics (an `assert!` failure: Aeneas label `.assertionFailure`) (`chunks(0)`). -/
theorem proto.codec.compress_with_max_zero (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val ≠ []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d 0#usize src dst = fail .assertionFailure := by
  unfold proto.codec.compress_with
  have hne : ¬ (alloc.vec.Vec.deref src).val = [] := by simpa [alloc.vec.Vec.deref] using hsrc
  have hz : core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN 0#usize = 0#usize := by
    apply UScalar.eq_of_val_eq; simp
  simp [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty, hne,
    core.cmp.min, hz, massert]

/-- `compress_with` with no deflate stream yet and a level above 10 panics when it creates one, i.e. when the first piece has at least `minCompressLength` bytes (flate2's `debug_assert!(level <= 10)`, `src/ffi/miniz_oxide.rs:153`: debug builds only, no panic in release). -/
theorem proto.codec.compress_with_level_panic (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0) (hlvl : 10 < lvl.level.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize max.val) src.val.length) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl none max src dst = fail .panic := by
  unfold proto.codec.compress_with
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  have hne : (alloc.vec.Vec.deref src).val ≠ [] := by simpa [alloc.vec.Vec.deref] using hsrc
  have hl0 : ¬ (alloc.vec.Vec.deref src).length = 0 := by
    simpa [Slice.length] using hne
  have hmin : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max).val = compChunkSize max.val := by
    simp only [core.cmp.impls.OrdUsize.min_val, hmp, compChunkSize]
  have hcs : 0 < compChunkSize max.val := by
    have : compChunkSize max.val = min (2 ^ 24 - 1) max.val := rfl
    omega
  have hnz : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max != 0#usize) = true := by
    have : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max).val ≠ 0 := by rw [hmin]; omega
    simpa [UScalar.eq_equiv] using this
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty, core.cmp.min,
    Std.bind_ok, hl0, decide_false, Bool.false_eq_true, ↓reduceIte, massert, hnz]
  unfold proto.codec.compress_with_loop
  rw [loop]
  apply PBUtil.bind_fail_left
  generalize hN : core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max = N at hmin
  simp only [proto.codec.compress_with_loop.body, proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref,
    Std.bind_ok, core.cmp.min]
  have hlt : (0#usize) < (alloc.vec.Vec.deref src).len := by
    have : 0 < (alloc.vec.Vec.deref src).length := by omega
    scalar_tac
  rw [ite_eq_left_of_eq_true _ _ (by simpa using hlt)]
  have hsl : (alloc.vec.Vec.deref src).length = src.val.length := by simp [Slice.length, alloc.vec.Vec.deref]
  refine PBUtil.bind_fail_of_spec (UScalar.sub_spec (by simp)) (fun i2 hi2 => ?_)
  have hmn : (core.cmp.impls.OrdUsize.min N i2).val = min (compChunkSize max.val) src.val.length := by
    simp only [core.cmp.impls.OrdUsize.min_val, hmin, hi2.1, Slice.len_val, hsl]; simp
  have hmax24 : compChunkSize max.val < 2 ^ 24 := by
    have : compChunkSize max.val = min (2 ^ 24 - 1) max.val := rfl
    omega
  have hU : 2 ^ 32 - 1 ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  refine PBUtil.bind_fail_of_spec (UScalar.add_spec (by simp [hmn]; omega)) (fun i3 hi3 => ?_)
  refine PBUtil.bind_fail_of_spec (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec _ _
    (by simp) (by simp [hi3, hmn, hsl])) (fun chunk hc => ?_)
  refine PBUtil.bind_fail_of_spec (UScalar.add_spec (by simp [hc.2, hi3, hmn]; omega)) (fun i5 hi5 => ?_)
  have hl0' : ¬ lvl.level.val = 0 := by omega
  have hbig' : chunk.len ≥ constants.MIN_COMPRESS_LENGTH := by
    have : chunk.len.val = min (compChunkSize max.val) src.val.length := by
      rw [Slice.len_val, hc.2]; simp [hi3, hmn]
    simp only [ge_iff_le, UScalar.le_equiv, constants.MIN_COMPRESS_LENGTH]
    simp only [minCompressLength] at hbig
    have h' : min (compChunkSize max.val) src.val.length ≥ 512 := hbig
    have h5 : (512#usize).val = 512 := by simp
    omega
  simp [proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve,
    proto.codec.trusted.compression_none, proto.codec.trusted.compression_eq, hl0', hbig',
    proto.codec.trusted.compress_new, hlvl]

/-- `compress_with(seq_id, compression, deflater, max_allowed_packet, src, dst)` on a non-empty `src`, whenever it does not panic: as `compress_spec`. A kept deflate stream is reused and never re-created, so the level is then not checked. The new stream is not described (it is opaque flate2 state). -/
theorem proto.codec.compress_with_spec (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0)
    (hlvl : d ≠ none ∨ lvl.level.val ≤ 10 ∨ Nat.min (compChunkSize max.val) src.val.length < minCompressLength)
    (h : dst.val.length + 8 * src.val.length ≤ Usize.max) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d max src dst ⦃ r _ src' dst' =>
      match r with
      | .Ok s =>
        s = byte (seq.val + (chunksOf (compChunkSize max.val) src.val).length) ∧ src'.val = [] ∧
        ∃ out, CompEncoding (d.getD (Trusted.compressNew lvl)) lvl.level.val (compChunkSize max.val) seq.val src.val out ∧ dst'.val = dst.val ++ out
      | .Err e =>
        (∃ ioe, e = .Io ioe) ∧ src' = src ∧
        ∃ k out, k < (chunksOf (compChunkSize max.val) src.val).length ∧ lvl.level.val ≠ 0 ∧
          minCompressLength ≤ ((chunksOf (compChunkSize max.val) src.val).getD k []).length ∧
          CompPacketsOf (d.getD (Trusted.compressNew lvl)) lvl.level.val seq.val ((chunksOf (compChunkSize max.val) src.val).take k) out ∧
          dst'.val = dst.val ++ out ⦄ := by
  unfold proto.codec.compress_with
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  have hne : (alloc.vec.Vec.deref src).val ≠ [] := by simpa [alloc.vec.Vec.deref] using hsrc
  have hl0 : ¬ (alloc.vec.Vec.deref src).length = 0 := by
    simpa [Slice.length] using hne
  have hmin : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max).val = compChunkSize max.val := by
    simp only [core.cmp.impls.OrdUsize.min_val, hmp, compChunkSize]
  have hcs : 0 < compChunkSize max.val := by
    have : compChunkSize max.val = min (2 ^ 24 - 1) max.val := rfl
    omega
  have hnz : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max != 0#usize) = true := by
    have : (core.cmp.impls.OrdUsize.min constants.MAX_PAYLOAD_LEN max).val ≠ 0 := by
      rw [hmin]; omega
    simpa [UScalar.eq_equiv] using this
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty, core.cmp.min,
    Std.bind_ok, hl0, decide_false, Bool.false_eq_true, ↓reduceIte, massert, hnz]
  apply spec_mono (cw_loop_spec lvl d src _ (by rw [hmin]; omega) seq dst
    (by rw [hmin]; exact hlvl) h)
  rintro ⟨r, d', s', d''⟩ hy
  simp only [CWPost, hmin] at hy
  exact hy

end mysql_common
