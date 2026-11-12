import Defs
import Proofs.Util.ParseBuf

/-! Statements for `fn packet_to_chunks` (spec file: `Specs/Proto/Codec.lean`). -/

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
private theorem vb_chunk_spec (v : VecBuf) : VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.chunk v ⦃ s => s.val = v.val ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.chunk, alloc.vec.Vec.deref]

open proto.codec.buf_model in
@[step]
private theorem vb_remaining_spec (v : VecBuf) : VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.remaining v ⦃ n => n.val = v.length ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.remaining]

open proto.codec.buf_model in
@[step]
private theorem inner_spec (packet dst : VecBuf) (k : Usize) (hk : k.val ≤ packet.length)
    (hd : dst.length + k.val ≤ Usize.max) :
    proto.codec.packet_to_chunks_loop0_loop0 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut packet dst k
      ⦃ p' d' => p'.val = packet.val.drop k.val ∧ d'.val = dst.val ++ packet.val.take k.val ⦄ := by
  unfold proto.codec.packet_to_chunks_loop0_loop0
  apply loop.spec_decr_nat (fun x => x.2.2.val)
    (fun x => x.2.2.val ≤ x.1.length ∧ x.2.1.length + x.2.2.val ≤ Usize.max ∧
      ∃ j, j + x.2.2.val = k.val ∧ x.1.val = packet.val.drop j ∧ x.2.1.val = dst.val ++ packet.val.take j)
  · rintro ⟨p, d, c⟩ ⟨hc, hdc, j, hj, hp, hd⟩
    unfold proto.codec.packet_to_chunks_loop0_loop0.body
    simp only [core.cmp.min]
    simp only at hc hdc hj hp hd
    have e1 : alloc.vec.Vec.length p = p.val.length := rfl
    have e2 : alloc.vec.Vec.length d = d.val.length := rfl
    step*
    · have hcl : chunk.len.val = p.val.length := by
        rw [Slice.len_val]; simp [Slice.length, chunk_post]
      have hmin : (core.cmp.impls.OrdUsize.min chunk.len c).val = c.val := by
        simp only [core.cmp.impls.OrdUsize.min_val, hcl]; omega
      rw [hmin] at chunk_len1_post s_post packet1_post s_post1
      have hc0 : 0 < c.val := by scalar_tac
      have e4 : alloc.vec.Vec.length dst1 = dst1.val.length := rfl
      have hsl : s.val.length = c.val := s_post1
      have hdl : dst1.val.length = d.val.length + c.val := by rw [dst1_post, List.length_append, hsl]
      refine ⟨by omega, by omega,
        ⟨j + c.val, by omega, by simp [packet1_post, hp, List.drop_drop], ?_⟩, by omega⟩
      simp [dst1_post, s_post, hd, hp, chunk_post, List.take_add]
  · exact ⟨hk, hd, 0, by simp, by simp, by simp⟩


private theorem hdr_bytes (L : Nat) (hL : L < 2 ^ 24) (s : Nat) (_hs : s < 256) (x : BitVec 32)
    (hx : x.toNat = L + s * 2 ^ 24) : x.toLEBytes.map (@UScalar.mk UScalarTy.U8) = leBytes 3 L ++ [byte s] := by
  have htl : x.toLEBytes = [BitVec.setWidth 8 x, BitVec.setWidth 8 (x >>> 8),
      BitVec.setWidth 8 (BitVec.setWidth 24 (x >>> 8) >>> 8),
      BitVec.setWidth 8 (BitVec.setWidth 16 (BitVec.setWidth 24 (x >>> 8) >>> 8) >>> 8)] := by
    simp [BitVec.toLEBytes]
  rw [htl]
  simp only [leBytes, byte, List.map, List.cons_append, List.nil_append, List.cons.injEq,
    UScalar.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp [hx, Nat.shiftRight_eq_div_pow] <;> omega

private theorem hdr_val (L : Usize) (hL : L.val < 2 ^ 24) (seq : U8) (i3 : U32)
    (hi3 : i3.val = seq.val <<< 24 % U32.size) :
    ((core.num.U32.to_le_bytes (UScalar.cast UScalarTy.U32 L ||| i3)).to_slice).val = leBytes 3 L.val ++ [byte seq.val] := by
  simp only [Array.to_slice, core.num.U32.to_le_bytes]
  have hs := seq.hBounds
  have hcast : (UScalar.cast UScalarTy.U32 L).val = L.val := by
    rw [UScalar.cast_val_eq]; simp; omega
  have hsh : seq.val <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]; simp at hs ⊢; omega
  have hv : (UScalar.cast UScalarTy.U32 L ||| i3).val = L.val + seq.val * 2 ^ 24 := by
    rw [UScalar.val_or, hcast, hi3, Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; simpa using hsh), Nat.lor_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.shiftLeft_eq]
    ring
  have := hdr_bytes L.val hL seq.val (by simpa using hs) (UScalar.cast UScalarTy.U32 L ||| i3).bv hv
  simpa using this

private theorem byte_congr (a b : Nat) (h : a % 256 = b % 256) : byte a = byte b := by
  unfold byte; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]; omega

private theorem frame_congr (L : Nat) : ∀ (s1 s2 : Nat) (p : List U8), p.length = L → s1 % 256 = s2 % 256 →
    frame s1 p = frame s2 p := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s1 s2 p hp hs
    conv_lhs => rw [frame]
    conv_rhs => rw [frame]
    split_ifs with h1
    · rw [byte_congr s1 s2 hs]
    · rw [byte_congr s1 s2 hs, ih (L - maxPayloadLen) (by simp [maxPayloadLen] at *; omega) (s1 + 1) (s2 + 1)
        (p.drop maxPayloadLen) (by simp; omega) (by omega)]

private theorem frame_len (L : Nat) : ∀ (s : Nat) (p : List U8), p.length = L →
    (frame s p).length = L + 4 * (L / maxPayloadLen + 1) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s p hp
    rw [frame]
    split_ifs with h1
    · simp only [List.length_append, List.length_cons, PBUtil.length_leBytes, hp]
      simp only [maxPayloadLen] at *; omega
    · have := ih (L - maxPayloadLen) (by simp [maxPayloadLen] at *; omega) (s + 1) (p.drop maxPayloadLen) (by simp; omega)
      simp only [List.length_append, List.length_cons, List.length_take, PBUtil.length_leBytes, this]
      simp only [maxPayloadLen] at *; omega

open proto.codec.buf_model in
private theorem body_spec (seq : U8) (packet dst : VecBuf) (hpos : 0 < packet.length)
    (hd : dst.length + 4 + Min.min packet.length maxPayloadLen ≤ Usize.max) :
    proto.codec.packet_to_chunks_loop0.body VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut seq packet dst
      ⦃ r => ∃ p1 d1 : VecBuf, r = .cont (byte (seq.val + 1), p1, d1) ∧
        p1.val = packet.val.drop (Min.min packet.length maxPayloadLen) ∧
        d1.val = dst.val ++ leBytes 3 (Min.min packet.length maxPayloadLen) ++ [byte seq.val] ++
          packet.val.take (Min.min packet.length maxPayloadLen) ⦄ := by
  unfold proto.codec.packet_to_chunks_loop0.body
  simp only [core.cmp.min, lift, core.num.U8.wrapping_add, core.convert.num.FromU32U8.from]
  have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
  have e1 : alloc.vec.Vec.length dst = dst.val.length := rfl
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  have hmin : ∀ i : Usize, i.val = packet.val.length →
      (core.cmp.impls.OrdUsize.min i constants.MAX_PAYLOAD_LEN).val = Min.min packet.val.length maxPayloadLen := by
    intro i hi; simp only [core.cmp.impls.OrdUsize.min_val, hi, hmp]
  step*
  all_goals have hsv : (BitVec.setWidth UScalarTy.U32.numBits seq.bv#uscalar).val = seq.val :=
    core.convert.num.FromU32U8.from_val_eq seq
  all_goals rw [hmin i i_post] at *
  · have hdl : dst1.val.length = dst.val.length + 4 := by
      rw [dst1_post, List.length_append, hdr_val _ (by rw [hmin i i_post]; simp only [maxPayloadLen]; omega) seq i3 (by rw [i3_post, hsv])]
      simp [PBUtil.length_leBytes]
    have : alloc.vec.Vec.length dst1 = dst1.val.length := rfl
    omega
  · refine ⟨packet1, dst2, rfl, packet1_post, ?_⟩
    rw [packet1_post1, dst1_post, hdr_val _ (by rw [hmin i i_post]; simp only [maxPayloadLen]; omega) seq i3 (by rw [i3_post, hsv])]
    simp [hmin i i_post]

private theorem frame_nil' (s : Nat) : frame s [] = leBytes 3 0 ++ [byte s] := by
  rw [frame, ite_eq_left (by simp [maxPayloadLen])]; rfl

private theorem frame_lt (s : Nat) (p : List U8) (h : p.length < maxPayloadLen) :
    frame s p = leBytes 3 p.length ++ byte s :: p := by
  rw [frame, ite_eq_left h]

private theorem frame_ge (s : Nat) (p : List U8) (h : ¬ p.length < maxPayloadLen) :
    frame s p = leBytes 3 maxPayloadLen ++ byte s :: p.take maxPayloadLen ++ frame (s + 1) (p.drop maxPayloadLen) := by
  rw [frame, ite_eq_right h]

open proto.codec.buf_model in
private theorem outer_spec (L : Nat) : ∀ (seq : U8) (packet dst : VecBuf), packet.length = L →
    dst.length + L + 4 * ((L + maxPayloadLen - 1) / maxPayloadLen) ≤ Usize.max →
    proto.codec.packet_to_chunks_loop0 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut seq packet dst
      ⦃ seq' p' d' => p'.val = [] ∧ seq'.val = (seq.val + (L + maxPayloadLen - 1) / maxPayloadLen) % 256 ∧
        d'.val ++ (if L % maxPayloadLen = 0 then leBytes 3 0 ++ [byte seq'.val] else []) =
          dst.val ++ frame seq.val packet.val ⦄ := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro seq packet dst hL hd
    unfold proto.codec.packet_to_chunks_loop0
    rw [loop]
    have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
    have e1 : alloc.vec.Vec.length dst = dst.val.length := rfl
    have hsb := seq.hBounds
    simp only [UScalarTy.numBits] at hsb
    by_cases hL0 : L = 0
    · have hp : packet.val = [] := by rw [← List.length_eq_zero_iff]; omega
      have hb : proto.codec.packet_to_chunks_loop0.body VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf
          VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut seq packet dst = ok (.done (seq, packet, dst)) := by
        unfold proto.codec.packet_to_chunks_loop0.body
        simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.remaining,
          alloc.vec.Vec.len, hp]
      simp only [hb, bind_ok]
      subst hL0
      simp only [WP.spec_ok]
      refine ⟨hp, ?_, ?_⟩
      · simp only [maxPayloadLen]; omega
      · rw [hp, frame_nil']; simp
    · obtain ⟨c, hcdef⟩ : ∃ c, Min.min packet.length maxPayloadLen = c := ⟨_, rfl⟩
      have hcL : c ≤ L := by omega
      have hcM : c ≤ maxPayloadLen := by omega
      have hc1 : 1 ≤ c := by simp only [maxPayloadLen] at *; omega
      have hcc : c = L ∨ c = maxPayloadLen := by omega
      have hcLM : c = L ↔ L < maxPayloadLen ∨ L = maxPayloadLen := by simp only [maxPayloadLen] at *; omega
      obtain ⟨k, hk⟩ : ∃ k, (L - c + maxPayloadLen - 1) / maxPayloadLen = k := ⟨_, rfl⟩
      have hceil : (L + maxPayloadLen - 1) / maxPayloadLen = 1 + k := by
        rw [← hk]; simp only [maxPayloadLen] at *; omega
      rw [hceil] at hd ⊢
      simp only []
      apply WP.spec_bind (body_spec seq packet dst (by omega) (by rw [hcdef]; omega))
      rintro r ⟨p1, d1, rfl, hp1, hd1⟩
      rw [hcdef] at hp1 hd1
      simp only
      have hp1l : alloc.vec.Vec.length p1 = L - c := by
        show p1.val.length = _; rw [hp1]; simp; omega
      have hd1l : alloc.vec.Vec.length d1 = dst.val.length + 4 + c := by
        show d1.val.length = _; rw [hd1]; simp [PBUtil.length_leBytes]; omega
      have := ih (L - c) (by omega) (byte (seq.val + 1)) p1 d1 hp1l (by rw [hk]; omega)
      unfold proto.codec.packet_to_chunks_loop0 at this
      rw [hk] at this
      apply WP.spec_mono this
      rintro ⟨seq', p', d'⟩ ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [h2, PBUtil.byte_val]; omega
      · by_cases hLM : L < maxPayloadLen
        · have hcL' : c = L := hcLM.mpr (Or.inl hLM)
          subst hcL'
          have hLm : c % maxPayloadLen ≠ 0 := by rw [Nat.mod_eq_of_lt hLM]; omega
          have hk0 : k = 0 := by rw [← hk]; simp only [maxPayloadLen] at *; omega
          subst hk0
          have hs' : byte seq'.val = byte (byte (seq.val + 1)).val := by
            rw [h2]; congr 1; simp [PBUtil.byte_val]
          have hp1e : p1.val = [] := by rw [hp1]; simp; omega
          rw [hp1e, frame_nil', Nat.sub_self, Nat.zero_mod, ite_eq_left rfl, hs'] at h3
          have h3' : d'.val = d1.val := List.append_cancel_right h3
          rw [ite_eq_right hLm, List.append_nil, h3', hd1, frame_lt _ _ (by omega), List.take_of_length_le (by omega)]
          simp [← hL]
        · have hcM' : c = maxPayloadLen := by omega
          subst hcM'
          have hmod : (L - maxPayloadLen) % maxPayloadLen = L % maxPayloadLen := by
            have : L = (L - maxPayloadLen) + maxPayloadLen := by omega
            conv_rhs => rw [this]
            rw [Nat.add_mod_right]
          rw [hmod, hd1, frame_congr _ (byte (seq.val + 1)).val (seq.val + 1) p1.val rfl
            (by rw [PBUtil.byte_val]; omega), hp1] at h3
          rw [h3, frame_ge seq.val packet.val (by omega)]
          simp

open proto.codec.buf_model in
@[step]
private theorem outer_spec' (seq : U8) (packet dst : VecBuf)
    (hd : dst.length + packet.length + 4 * ((packet.length + maxPayloadLen - 1) / maxPayloadLen) ≤ Usize.max) :
    proto.codec.packet_to_chunks_loop0 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut seq packet dst
      ⦃ seq' p' d' => p'.val = [] ∧ seq'.val = (seq.val + (packet.length + maxPayloadLen - 1) / maxPayloadLen) % 256 ∧
        d'.val ++ (if packet.length % maxPayloadLen = 0 then leBytes 3 0 ++ [byte seq'.val] else []) =
          dst.val ++ frame seq.val packet.val ⦄ :=
  outer_spec packet.length seq packet dst rfl hd

private theorem hdr_val0 (seq : U8) (i6 : U32) (hi6 : i6.val = seq.val <<< 24 % U32.size) :
    ((core.num.U32.to_le_bytes i6).to_slice).val = leBytes 3 0 ++ [byte seq.val] := by
  simp only [Array.to_slice, core.num.U32.to_le_bytes]
  have hs := seq.hBounds
  have hsh : seq.val <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]; simp at hs ⊢; omega
  have hv : i6.val = 0 + seq.val * 2 ^ 24 := by
    rw [hi6, Nat.mod_eq_of_lt (by simp [U32.size, U32.numBits]; simpa using hsh), Nat.shiftLeft_eq]; ring
  have := hdr_bytes 0 (by norm_num) seq.val (by simpa using hs) i6.bv hv
  simpa using this

/-- `packet_to_chunks(seq_id, packet, dst)`: consumes the whole packet and appends its chunks (`frame`: chunks of at most `2^24 - 1` bytes, each with a 3-byte length and the sequence id, starting at `seq_id` and wrapping; an empty last chunk iff the length is a multiple of `2^24 - 1`); returns the next sequence id. -/
@[step]
theorem proto.codec.packet_to_chunks_spec (seq : U8) (packet dst : proto.codec.buf_model.VecBuf) (h : dst.length + (frame seq.val packet.val).length ≤ Usize.max) :
    proto.codec.packet_to_chunks proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq packet dst ⦃ seq' packet' dst' =>
      seq'.val = (seq.val + frameCount packet.length) % 256 ∧ packet'.val = [] ∧
      dst'.val = dst.val ++ frame seq.val packet.val ⦄ := by
  have hfl := frame_len packet.length seq.val packet.val rfl
  rw [hfl] at h
  unfold proto.codec.packet_to_chunks
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  simp only [core.num.Usize.is_multiple_of, UScalar.is_multiple_of,
    proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve, lift,
    core.num.U8.wrapping_add, core.convert.num.FromU32U8.from]
  have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
  have e1 : alloc.vec.Vec.length dst = dst.val.length := rfl
  have hceil : (packet.length + maxPayloadLen - 1) / maxPayloadLen ≤ packet.length / maxPayloadLen + 1 := by
    simp only [maxPayloadLen]; omega
  have hceil2 : packet.length % maxPayloadLen = 0 →
      (packet.length + maxPayloadLen - 1) / maxPayloadLen = packet.length / maxPayloadLen := by
    simp only [maxPayloadLen]; omega
  have hceil3 : packet.length % maxPayloadLen ≠ 0 →
      (packet.length + maxPayloadLen - 1) / maxPayloadLen = packet.length / maxPayloadLen + 1 := by
    simp only [maxPayloadLen]; omega
  step*
  · simp [hmp, maxPayloadLen]
  · have hm : packet.length % maxPayloadLen = 0 := by simp_all
    simp only [hm, ite_true] at seq_id1_post2
    have := congrArg List.length seq_id1_post2
    simp only [List.length_append, hfl, PBUtil.length_leBytes, List.length_singleton] at this
    have : alloc.vec.Vec.length dst2 = dst2.val.length := rfl
    have : (core.num.U32.to_le_bytes i6).to_slice.length = 4 := by simp [Slice.length]
    omega
  · have hm : packet.length % maxPayloadLen = 0 := by simp_all
    simp only [hm, ite_true] at seq_id1_post2
    have hsv : (BitVec.setWidth UScalarTy.U32.numBits seq_id1.bv#uscalar).val = seq_id1.val :=
      core.convert.num.FromU32U8.from_val_eq seq_id1
    refine ⟨?_, seq_id1_post, ?_⟩
    · have : (UScalar.wrapping_add seq_id1 1#u8) = byte (seq_id1.val + 1) := by
        simp only [UScalar.wrapping_add, byte]; congr 1
      rw [this, PBUtil.byte_val, seq_id1_post1, hceil2 hm, frameCount]; try omega
    · rw [dst3_post, hdr_val0 seq_id1 i6 (by rw [i6_post, hsv]), ← seq_id1_post2]
  · have hm : packet.length % maxPayloadLen ≠ 0 := by simp_all
    simp only [hm, ite_false, List.append_nil] at seq_id1_post2
    refine ⟨?_, seq_id1_post, seq_id1_post2⟩
    rw [seq_id1_post1, hceil3 hm, frameCount]

end mysql_common
