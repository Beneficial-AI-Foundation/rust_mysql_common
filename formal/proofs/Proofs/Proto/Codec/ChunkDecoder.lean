import Defs
import Proofs.Util.ParseBuf

/-! Statements for `enum ChunkDecoder and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open proto.codec.buf_model in
@[step]
private theorem vb_advance_spec (src : VecBuf) (cnt : Usize) (h : cnt.val ≤ src.length) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance src cnt ⦃ r => r.val = src.val.drop cnt.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance
  step*
  subst_vars; assumption

open proto.codec.buf_model in
@[step]
private theorem vb_put_slice_spec (dst : VecBuf) (s : Slice U8) (h : dst.length + s.length ≤ Usize.max) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice dst s ⦃ r => r.val = dst.val ++ s.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp only [dite_eq_left h]
  have := List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val) (by intros; rfl)
  obtain ⟨l, hl, hp⟩ := PBUtil.spec_eq_ok this
  simp [hl, hp.1]

open proto.codec.buf_model in
@[step]
private theorem vb_deref (v : VecBuf) : VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref v ⦃ s => s.val = v.val ⦄ := by
  simp [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, alloc.vec.Vec.deref]

open proto.codec.buf_model in
@[step]
private theorem vb_as_ref (v : VecBuf) : VecBuf.Insts.CoreConvertAsRefSliceU8.as_ref v ⦃ s => s.val = v.val ⦄ := by
  simp [VecBuf.Insts.CoreConvertAsRefSliceU8.as_ref, alloc.vec.Vec.deref]

open proto.codec.buf_model in
@[step]
private theorem decode_chunk (seq : U8) (needed : NonZeroUsize) (src dst : VecBuf) (max : Usize)
    (h : chunkStepFits (.chunk seq needed.val) src.val dst.val) :
    proto.codec.ChunkDecoder.decode VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.CoreConvertAsRefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut (.Chunk seq needed) src dst max ⦃ r cd src' dst' =>
      (r, ChunkState.of cd, src'.val, dst'.val) = chunkStep (.chunk seq needed.val) src.val dst.val max.val ∧
      ((ChunkState.chunk seq needed.val).Valid → (ChunkState.of cd).Valid) ⦄ := by
  obtain ⟨h1, h2⟩ := h
  rw [proto.codec.ChunkDecoder.decode]
  simp only [proto.codec.buf_model.NonZeroUsize.get, constants.MAX_PAYLOAD_LEN]
  step*
  all_goals simp_all [chunkStep, ChunkState.of, ChunkState.Valid, List.drop_drop, maxPayloadLen, Slice.length]
  all_goals omega


/-- `decode(src, dst, max_allowed_packet)`: total; exactly one step of `chunkStep` (needs more input, a chunk read, or `PacketTooLarge`), with the new state, input and output. The only hypothesis is that the lengths computed fit in a `usize` (`chunkStepFits`; a valid state with `dst.length + 2^24 ≤ usize::MAX` is enough, `chunkStepFits_of_valid`). From a valid state the new state is again valid. -/
theorem proto.codec.ChunkDecoder.decode_spec (self : proto.codec.ChunkDecoder) (src dst : proto.codec.buf_model.VecBuf)
    (max : Usize) (h : chunkStepFits (ChunkState.of self) src.val dst.val) :
    proto.codec.ChunkDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, ChunkState.of cd, src'.val, dst'.val) = chunkStep (ChunkState.of self) src.val dst.val max.val ∧
      ((ChunkState.of self).Valid → (ChunkState.of cd).Valid) ⦄ := by
  cases self with
  | Chunk seq needed => exact decode_chunk seq needed src dst max h
  | Idle =>
    simp only [ChunkState.of, chunkStepFits] at h
    rw [proto.codec.ChunkDecoder.decode]
    simp only [proto.codec.buf_model.NonZeroUsize.get, proto.codec.buf_model.NonZeroUsize.new]
    step*
    · simp_all [chunkStep, ChunkState.of, ChunkState.Valid]
    · have hl : 4 ≤ src.length := by
        have : s.length = src.length := by simp [Slice.length, alloc.vec.Vec.length, s_post]
        scalar_tac
      obtain ⟨a, b, c, d, r, hsrc⟩ : ∃ a b c d r, src.val = a :: b :: c :: d :: r := by
        match hh : src.val with
        | a :: b :: c :: d :: r => exact ⟨a, b, c, d, r, rfl⟩
        | [] | [_] | [_, _] | [_, _, _] => simp [alloc.vec.Vec.length, hh] at hl
      have hrl : raw_chunk_len.val = leNat [a, b, c] := by
        rw [raw_chunk_len_post, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by cases System.Platform.numBits_eq <;> simp [*])]
        have : i4.val = i4.bv.toNat := rfl
        rw [this, i4_post, PBUtil.fromLEBytes_cast_toNat]
        simp only [Array.make_val]
        have := PBUtil.leNat_append_zeros [a, b, c] 1
        simp_all
      have hlt : leNat [a, b, c] < 2 ^ 24 := by
        have := PBUtil.leNat_lt [a, b, c]; simpa using this
      have hseq : seq_id = d := by simp_all
      have hfit : dst.val.length + leNat [a, b, c] ≤ Usize.max := by
        have := h hl; simpa [hsrc] using this
      by_cases h0 : leNat [a, b, c] = 0
      · have : raw_chunk_len = 0#usize := by scalar_tac
        simp only [this, bne_self_eq_false, Bool.false_eq_true, ite_false]
        step*
        simp_all [chunkStep, ChunkState.of, ChunkState.Valid]
      · have : (raw_chunk_len != 0#usize) = true := by simp; scalar_tac
        simp only [this, ite_true]
        have hpos : 0 < leNat [a, b, c] := Nat.pos_of_ne_zero h0
        have hfit' : chunkStepFits (.chunk seq_id raw_chunk_len.val) src.val dst.val := by
          have hmax : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
          exact ⟨by rw [hrl]; omega, fun _ => by rw [hrl]; exact hfit⟩
        step*
        all_goals simp_all [chunkStep, ChunkState.of, ChunkState.Valid]
        all_goals (split_ifs <;> first | rfl | omega)
end mysql_common
