import Defs
import Proofs.Util.CompCodec
import Proofs.Proto.Codec.CompData
import Proofs.Defs.LemmasComp

/-! Statements for `enum CompDecoder and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

/-! Helper specs of `CompDecoder::decode_with` (any state and inflate stream), used by the
`CompPacketCodec` proofs. -/

namespace mysql_common.CompCodec
open proto.codec.buf_model
open WP

theorem inflateList_slice (i : flate2.mem.Decompress) (s : Slice U8) (p : Usize) :
    inflateList i s.val p.val =
      match Trusted.inflateResult i s p with
      | .Ok v => .Ok v.val
      | .Err e => .Err e := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  unfold inflateList
  rw [dite_eq_left hs]
  have e1 : Slice.from s.val hs = s := Slice.val_from s hs
  have e2 : (⟨BitVec.ofNat _ p.val⟩ : Usize) = p := by
    apply UScalar.eq_of_val_eq; show (BitVec.ofNat _ p.val).toNat = p.val; simp
  rw [e1, e2]
  rfl

@[step]
theorem decode_packet_spec (seq : U8) (d : proto.codec.CompData) (src dst : VecBuf) (max : Usize)
    (inf : Option flate2.mem.Decompress)
    (h : compStepFits (CompState.of (.Packet seq d)) dst.val) :
    proto.codec.CompDecoder.decode_with VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut
      (.Packet seq d) src dst max inf ⦃ r cd src' dst' _ =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList (inf.getD Trusted.decompressNew)) (CompState.of (.Packet seq d)) src.val dst.val max.val ⦄ := by
  rw [proto.codec.CompDecoder.decode_with]
  simp only [proto.codec.CompData.needed_eq]
  cases d with
  | Uncompressed n =>
    obtain ⟨h1, h2, -⟩ := h
    simp only [CompState.of] at h1 h2 ⊢
    step*
    · have hl : 7 + n.val ≤ src.val.length := by
        have := ‹s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      simp [s1_post, src1_post, Slice.length]; omega
    · have hl : 7 + n.val ≤ src.val.length := by
        have := ‹s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      step with proto.codec.CompData.write_payload_spec (.Uncompressed n) s2 dst inf (by simp [s2_post1]; omega) as ⟨r, dst1, inf1, hp⟩
      obtain ⟨rfl, hd1, rfl⟩ := hp
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step*
      simp [compStep, hl, src2_post, src1_post, hd1, s2_post, s1_post, List.drop_drop, List.slice]
    · have hl : ¬ 7 + n.val ≤ src.val.length := by
        have := ‹¬ s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      simp [compStep, hl]
  | Compressed n p =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [CompState.of, Option.getD_some] at h1 h2 h3 ⊢
    step*
    · have hl : 7 + n.val ≤ src.val.length := by
        have := ‹s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      simp [s1_post, src1_post, Slice.length]; omega
    · have hl : 7 + n.val ≤ src.val.length := by
        have := ‹s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      step with proto.codec.CompData.write_payload_spec (.Compressed n p) s2 dst inf (by simp; omega) as ⟨r, dst1, inf1, hp⟩
      have hz : s2.val = List.take n.val (List.drop 7 src.val) := by simp [s2_post, s1_post, src1_post, List.slice]
      have hi := inflateList_slice (inf.getD Trusted.decompressNew) s2 p
      rw [hz] at hi
      obtain ⟨-, hp⟩ := hp
      simp only [compStep, hl, ↓reduceIte, hi]
      cases hr : Trusted.inflateResult (inf.getD Trusted.decompressNew) s2 p with
      | Ok v =>
        rw [hr] at hp
        obtain ⟨rfl, hd1⟩ := hp
        simp only [core.result.Result.Insts.CoreOpsTry.branch]
        step*
        simp [src2_post, src1_post, hd1, List.drop_drop]
      | Err e =>
        rw [hr] at hp
        obtain ⟨rfl, rfl⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from, src1_post]
    · have hl : ¬ 7 + n.val ≤ src.val.length := by
        have := ‹¬ s.len ≥ i2›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val, Slice.length, s_post, i2_post] at this; exact this
      simp [compStep, hl]

theorem compStep_idle_hdr (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (src dst : List U8) (max cl : Nat) (sq : U8) (pl : Nat) (hl : 7 ≤ src.length)
    (hh : compHeaderRead src = (cl, sq, pl)) :
    compStep inf .idle src dst max =
      if max < Nat.max cl pl then (.Err .PacketTooLarge, .idle, src, dst)
      else if cl = 0 then
        (if pl = 0 then (.Ok (some (.Last sq)), .idle, src.drop 7, dst)
         else (.Err .BadCompressedPacketHeader, .idle, src, dst))
      else compStep inf (.packet sq cl (if pl = 0 then none else some pl)) src dst max := by
  have : ¬ src.length < 7 := by omega
  simp only [compStep, hh, this, ↓reduceIte]

theorem decode_idle_spec (src dst : VecBuf) (max : Usize)
    (inf : Option flate2.mem.Decompress)
    (h : compStepFits CompState.idle dst.val) :
    proto.codec.CompDecoder.decode_with VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut
      .Idle src dst max inf ⦃ r cd src' dst' _ =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList (inf.getD Trusted.decompressNew)) CompState.idle src.val dst.val max.val ⦄ := by
  simp only [compStepFits] at h
  rw [proto.codec.CompDecoder.decode_with]
  simp only [proto.codec.CompData.new_eq]
  step*
  · simp_all [compStep, CompState.of]
  all_goals
    have hl : 7 ≤ src.val.length := by
      have : s.length = src.val.length := by simp [Slice.length, s_post]
      scalar_tac
    obtain ⟨a, b, c, d, e, f, g, rr, hsrc⟩ : ∃ a b c d e f g rr, src.val = a :: b :: c :: d :: e :: f :: g :: rr := by
      match hh : src.val with
      | a :: b :: c :: d :: e :: f :: g :: rr => exact ⟨a, b, c, d, e, f, g, rr, rfl⟩
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] => simp [hh] at hl
    have hcl : compressed_len.val = leNat [a, b, c] := by
      rw [compressed_len_post, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by cases System.Platform.numBits_eq <;> simp [*])]
      have : i4.val = i4.bv.toNat := rfl
      rw [this, i4_post, PBUtil.fromLEBytes_cast_toNat]
      simp only [Array.make_val]
      have := PBUtil.leNat_append_zeros [a, b, c] 1
      simp_all
    have hpl : uncompressed_len.val = leNat [e, f, g] := by
      rw [uncompressed_len_post, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by cases System.Platform.numBits_eq <;> simp [*])]
      have : i8.val = i8.bv.toNat := rfl
      rw [this, i8_post, PBUtil.fromLEBytes_cast_toNat]
      simp only [Array.make_val]
      have := PBUtil.leNat_append_zeros [e, f, g] 1
      simp_all
    have hseq : seq_id = d := by simp_all
    have hb1 : leNat [a, b, c] < 2 ^ 24 := by have := PBUtil.leNat_lt [a, b, c]; simpa using this
    have hb2 : leNat [e, f, g] < 2 ^ 24 := by have := PBUtil.leNat_lt [e, f, g]; simpa using this
    have hhdr : compHeaderRead src.val = (leNat [a, b, c], d, leNat [e, f, g]) := by
      simp [compHeaderRead, hsrc]
    rw [hcl, hpl] at cf_post
  all_goals
    have hst := compStep_idle_hdr (inflateList (inf.getD Trusted.decompressNew)) src.val dst.val max.val _ _ _ hl hhdr
    clear i1_post i2_post i3_post i5_post i6_post i7_post i4_post i8_post compressed_len_post
      uncompressed_len_post seq_id_post
    subst hseq
    try rw [hst]
    clear hst hhdr
    generalize leNat [a, b, c] = cl at *
    generalize leNat [e, f, g] = pl at *
    clear hsrc s_post
    split_ifs at cf_post ⊢ <;> simp_all [CompState.of]
  all_goals
    subst_vars
    dsimp only
  all_goals
    have : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
    simp only [compStepFits, Option.getD_none, Option.getD_some]; omega

theorem decode_with_spec (st : proto.codec.CompDecoder) (src dst : VecBuf) (max : Usize)
    (inf : Option flate2.mem.Decompress)
    (h : compStepFits (CompState.of st) dst.val) :
    proto.codec.CompDecoder.decode_with VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut
      st src dst max inf ⦃ r cd src' dst' _ =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList (inf.getD Trusted.decompressNew)) (CompState.of st) src.val dst.val max.val ⦄ := by
  cases st with
  | Packet seq d => exact decode_packet_spec seq d src dst max inf h
  | Idle => exact decode_idle_spec src dst max inf h

end mysql_common.CompCodec

namespace mysql_common

/-- `decode(src, dst, max_allowed_packet)`: total. It is exactly one step of `compStep`, inflating with a new stream, and gives the new state, input and output. The step's outcome is one of: more input needed, a compressed packet read, `PacketTooLarge`, `BadCompressedPacketHeader`, or an `Io` error from inflating. The only hypothesis is that the lengths computed fit in a `usize` (`compStepFits`). From a valid state, the new state is again valid. -/
theorem proto.codec.CompDecoder.decode_spec (self : proto.codec.CompDecoder) (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : compStepFits (CompState.of self) dst.val) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList Trusted.decompressNew) (CompState.of self) src.val dst.val max.val ∧
      ((CompState.of self).Valid → (CompState.of cd).Valid) ⦄ := by
  unfold proto.codec.CompDecoder.decode
  obtain ⟨⟨r, cd, s', d', i'⟩, hv, hp⟩ := PBUtil.spec_eq_ok (CompCodec.decode_with_spec self src dst max none h)
  simp only [WP.uncurry'_pair, Option.getD_none] at hp
  simp [hv]
  refine ⟨hp, fun hval => ?_⟩
  have := compStep_valid (inflateList Trusted.decompressNew) _ src.val dst.val max.val hval
  rw [← hp] at this
  exact this

/-- Round trip for one packet. An idle decoder reads a compressed packet in the form the crate writes it (`compPacket`: stored, or a successful deflate of the piece) back to the piece. The result is `Ok(Last(seq))`, exactly the packet is consumed, and the decoder is idle again. (This rests on `Trusted.inflate_deflate`.) -/
theorem proto.codec.CompDecoder.decode_compPacket (seq : U8) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = compPacket seq.val chunk zo ++ tail) (max : Usize)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val) (h : dst.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut .Idle src dst max ⦃ r cd src' dst' =>
      r = .Ok (some (.Last seq)) ∧ cd = .Idle ∧ src'.val = tail ∧ dst'.val = dst.val ++ chunk ⦄ := by
  obtain ⟨⟨r, cd, s', d'⟩, hv, hp, -⟩ := PBUtil.spec_eq_ok (proto.codec.CompDecoder.decode_spec .Idle src dst max h)
  rw [hv]
  simp only [WP.spec_ok, WP.uncurry'_pair] at hp ⊢
  simp only [CompState.of, hsrc, compStep_compPacket Trusted.decompressNew seq.val chunk zo hz tail dst.val max.val hmax,
    Prod.mk.injEq] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, h3, h4⟩
  · have : seq.val < 256 := by scalar_tac
    rw [h1]; congr; apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; omega
  · cases cd with
    | Idle => rfl
    | Packet s d => cases d <;> simp at h2

end mysql_common
