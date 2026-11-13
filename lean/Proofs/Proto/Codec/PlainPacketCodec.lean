import Defs
import Proofs.Util.ParseBuf
import Proofs.Defs.LemmasCF
import Proofs.Proto.Codec.ChunkDecoder
import Proofs.Proto.Codec.PacketToChunks

/-! Statements for `struct PlainPacketCodec and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem wrap_one (x : U8) : core.num.U8.wrapping_add x 1#u8 = byte (x.val + 1) := by
  simp only [core.num.U8.wrapping_add, UScalar.wrapping_add, byte]
  congr 1

private theorem chunkStep_sizes (st : ChunkState) (src dst : List U8) (max : Nat) :
    (chunkStep st src dst max).2.2.2.length + (chunkStep st src dst max).2.2.1.length ≤ dst.length + src.length ∧
    (∀ s, (chunkStep st src dst max).1 = .Ok (some (.Middle s)) →
      (chunkStep st src dst max).2.2.1.length + 4 ≤ src.length) := by
  unfold chunkStep
  cases st <;> simp only <;> split_ifs <;> simp <;> omega

private theorem chunkStep_some_idle (st : ChunkState) (src dst : List U8) (max : Nat) :
    ∀ info, (chunkStep st src dst max).1 = .Ok (some info) → (chunkStep st src dst max).2.1 = .idle := by
  unfold chunkStep
  cases st <;> simp only <;> split_ifs <;> simp

open proto.codec.buf_model in
private theorem decode_aux (n : Nat) : ∀ (self : proto.codec.PlainPacketCodec)
    (_hv : ∀ seq needed, self.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max)
    (src dst : VecBuf) (max : Usize) (comp : Option U8)
    (_h : dst.length + src.length + 2 ^ 24 ≤ Usize.max) (_hn : src.length < n),
    proto.codec.PlainPacketCodec.decode VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.CoreConvertAsRefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp ⦄ := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro self hv src dst max comp h hn
    rw [proto.codec.PlainPacketCodec.decode]
    have e1 : alloc.vec.Vec.length dst = dst.val.length := rfl
    have e2 : alloc.vec.Vec.length src = src.val.length := rfl
    have hfit : chunkStepFits (ChunkState.of self.chunk_decoder) src.val dst.val := by
      cases hcd : self.chunk_decoder with
      | Idle =>
        intro _
        have := PBUtil.leNat_lt (src.val.take 3)
        have : 2 ^ (8 * (src.val.take 3).length) ≤ 2 ^ 24 :=
          Nat.pow_le_pow_right (by norm_num) (by simp; omega)
        omega
      | Chunk seq needed => exact ⟨hv seq needed hcd, fun _ => by omega⟩
    obtain ⟨⟨r, cd, src1, dst1⟩, heq, hc, _⟩ :=
      PBUtil.spec_eq_ok (proto.codec.ChunkDecoder.decode_spec self.chunk_decoder src dst max hfit)
    have hidle := chunkStep_some_idle (ChunkState.of self.chunk_decoder) src.val dst.val max.val
    rw [← hc] at hidle
    simp only at hidle
    have hsz := chunkStep_sizes (ChunkState.of self.chunk_decoder) src.val dst.val max.val
    rw [← hc] at hsz
    simp only at hsz
    have hpd : plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp =
        plainDecodeAux (src.val.length + 1) self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp := rfl
    rw [hpd, plainDecodeAux, ← hc, heq]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rcases r with ((_ | info) | e)
    · simp
    · rcases info with s | s
      all_goals dsimp only
      all_goals simp only [proto.codec.ChunkInfo.seq_id, chunkInfoSeq, bind_ok, lift, wrap_one,
        VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty, bne_iff_ne, ne_eq,
        decide_eq_true_eq]
      · -- Middle
        have hlt := hsz.2 s rfl
        have hlen1 : (alloc.vec.Vec.deref src1).length = src1.val.length := by
          simp [alloc.vec.Vec.deref, Slice.length]
        have hderef : (alloc.vec.Vec.deref src1).val = src1.val := by simp [alloc.vec.Vec.deref]
        by_cases hemp : src1.val = []
        · have : (alloc.vec.Vec.deref src1).length = 0 := by simp [hlen1, hemp]
          by_cases hs' : self.seq_id = s
          · subst hs'; simp [hemp, hderef]
          · cases comp with
            | none =>
              have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
              simp [hs]
            | some c =>
              have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
              by_cases hcs : c = s
              · subst hcs; simp [hs, hemp, hderef]
              · have hcs' : ¬ c.val = s.val := fun h => hcs (UScalar.eq_of_val_eq h)
                simp [hs, hcs']
        · have : (alloc.vec.Vec.deref src1).length ≠ 0 := by simp [hlen1, hemp]
          have e3 : alloc.vec.Vec.length dst1 = dst1.val.length := rfl
          have e4 : alloc.vec.Vec.length src1 = src1.val.length := rfl
          have hfuel := plainDecodeAux_fuel src.val.length (byte (s.val + 1)) (ChunkState.of cd) src1.val dst1.val max.val comp (by omega)
          have hrec := ih { seq_id := byte (s.val + 1), chunk_decoder := cd }
            (by intro seq needed hcd
                have := hidle _ rfl
                simp only at hcd; subst hcd
                simp [ChunkState.of] at this) src1 dst1 max comp (by omega) (by omega)
          by_cases hs' : self.seq_id = s
          · subst hs'; simp [hemp, hfuel, hderef]; exact hrec
          · cases comp with
            | none =>
              have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
              simp [hs]
            | some c =>
              have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
              by_cases hcs : c = s
              · subst hcs; simp [hs, hemp, hfuel, hderef]; exact hrec
              · have hcs' : ¬ c.val = s.val := fun h => hcs (UScalar.eq_of_val_eq h)
                simp [hs, hcs']
      · -- Last
        by_cases hs' : self.seq_id = s
        · subst hs'
          simp
        · cases comp with
          | none =>
              have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
              simp [hs]
          | some c =>
            have hs : ¬ self.seq_id.val = s.val := fun h => hs' (UScalar.eq_of_val_eq h)
            by_cases hcs : c = s
            · subst hcs; simp [hs]
            · have hcs' : ¬ c.val = s.val := fun h => hcs (UScalar.eq_of_val_eq h)
              simp [hs, hcs']
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


open proto.codec.buf_model in
private theorem plainDecodeAux_sizes (n : Nat) : ∀ (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8),
    (plainDecodeAux n seq st src dst max comp).2.2.2.2.length + (plainDecodeAux n seq st src dst max comp).2.2.2.1.length ≤
      dst.length + src.length := by
  induction n with
  | zero => intros; simp [plainDecodeAux]
  | succ n ih =>
    intro seq st src dst max comp
    have hsz := (chunkStep_sizes st src dst max).1
    simp only [plainDecodeAux]
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rw [hc] at hsz
    simp only at hsz
    rcases r with ((_ | info) | e)
    · simp; omega
    · cases info with
      | Last _ => simp only; split_ifs <;> simp <;> omega
      | Middle s0 =>
        simp only; split_ifs
        all_goals first
          | (simp; omega)
          | (have := ih (byte ((chunkInfoSeq (.Middle s0)).val + 1)) st' src' dst' max comp; omega)
    · simp; omega

/-- `reset_seq_id`: the sequence id becomes 0. -/
theorem proto.codec.PlainPacketCodec.reset_seq_id_eq (self : proto.codec.PlainPacketCodec) :
    proto.codec.PlainPacketCodec.reset_seq_id self = ok { self with seq_id := 0#u8 } := by
  rfl

/-- `encode(packet, dst, max_allowed_packet)`: `PacketTooLarge`, nothing changed, if the packet is longer than `max_allowed_packet`; otherwise appends its chunks from the codec's sequence id (`frame`), consumes the packet, and advances the sequence id by the number of chunks. -/
theorem proto.codec.PlainPacketCodec.encode_spec (self : proto.codec.PlainPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : max.val < packet.length ∨ dst.length + (frame self.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r codec packet' dst' =>
      if max.val < packet.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with seq_id := byte (self.seq_id.val + frameCount packet.length) } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame self.seq_id.val packet.val ⦄ := by
  unfold proto.codec.PlainPacketCodec.encode
  simp only [proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.remaining,
    alloc.vec.Vec.len]
  by_cases hm : max.val < packet.length
  · simp [hm]
  · have hb := h.resolve_left hm
    simp only [hm, ite_false]
    have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
    step*
    have hi1 : i1 = byte (self.seq_id.val + frameCount (alloc.vec.Vec.length packet)) := by
      apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; omega
    simp_all

/-- `decode(src, dst, max_allowed_packet, comp_seq_id)`: total; exactly `plainDecode` (chunks read with `chunkStep` until the last chunk of a packet, `Ok(true)`, or more input is needed, `Ok(false)`, or an error: `PacketTooLarge`, or `PacketsOutOfSync` for a chunk whose sequence id is neither the expected one nor `comp_seq_id`). The decoder state need not be one the decoder produces: a pending length only has to satisfy `4 + needed ≤ usize::MAX` (`hv`). From a valid state the new state is again valid. -/
theorem proto.codec.PlainPacketCodec.decode_spec (self : proto.codec.PlainPacketCodec)
    (hv : ∀ seq needed, self.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (comp : Option U8)
    (h : dst.length + src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp ∧
      ((ChunkState.of self.chunk_decoder).Valid → (ChunkState.of codec.chunk_decoder).Valid) ⦄ := by
  apply WP.spec_mono (decode_aux (src.length + 1) self hv src dst max comp h (by omega))
  rintro ⟨r, codec, src', dst'⟩ heq
  refine ⟨heq, fun hval => ?_⟩
  have := plainDecode_valid self.seq_id _ hval src.val dst.val max.val comp
  rw [← heq] at this
  exact this

/-- Headline round trip: an idle codec decodes the chunks of a payload (`frame`, as `encode` writes them) starting at its sequence id into an empty `dst`: the whole payload, `Ok(true)`, the input after the chunks left, the sequence id advanced by the number of chunks, the decoder idle again. -/
theorem proto.codec.PlainPacketCodec.decode_frame (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame self.seq_id.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
      codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄ := by
  have hd0 : alloc.vec.Vec.length dst = 0 := by simp [alloc.vec.Vec.length, hdst]
  apply WP.spec_mono (proto.codec.PlainPacketCodec.decode_spec self (by rw [hidle]; simp)
    src dst max comp (by omega))
  rintro ⟨r, codec, src', dst'⟩ ⟨heq, _⟩
  rw [hidle, hsrc, hdst] at heq
  simp only [ChunkState.of] at heq
  rw [plainDecode_frame self.seq_id p tail max.val hmax comp] at heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨h1, h2, h3, h4, h5⟩ := heq
  refine ⟨h1, h2, ?_, h4, h5⟩
  cases hcd : codec.chunk_decoder <;> simp_all [ChunkState.of]

/-- Incremental decoding: on a strict prefix of the chunks of a payload, an idle codec reports that more input is needed (`Ok(false)`), never an error; the state it leaves is `plainDecode`'s (see `decode_resume` for continuing). -/
theorem proto.codec.PlainPacketCodec.decode_prefix (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok false ∧
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id ChunkState.idle ((frame self.seq_id.val p).take k) [] max.val comp ⦄ := by
  have hd0 : alloc.vec.Vec.length dst = 0 := by simp [alloc.vec.Vec.length, hdst]
  apply WP.spec_mono (proto.codec.PlainPacketCodec.decode_spec self (by rw [hidle]; simp)
    src dst max comp (by omega))
  rintro ⟨r, codec, src', dst'⟩ ⟨heq, _⟩
  rw [hidle, hsrc, hdst] at heq
  simp only [ChunkState.of] at heq
  refine ⟨?_, heq⟩
  rcases hpd : plainDecode self.seq_id .idle ((frame self.seq_id.val p).take k) [] max.val comp with
    ⟨r0, seq1, st1, src1, dst1⟩
  have := (plainDecode_resume self.seq_id p [] k hk max.val hmax comp r0 seq1 st1 src1 dst1 hpd).1
  rw [hpd] at heq
  simp only [Prod.mk.injEq] at heq
  rw [heq.1, this]

/-- Resumption: after decoding a strict prefix of the chunks of a payload (`Ok(false)`), calling `decode` again with the returned codec and output, on what the first call left of the input followed by the rest of the chunks (and anything after), completes the packet: `Ok(true)`, the whole payload, the sequence id advanced by the number of chunks, the decoder idle, the input after the chunks left. -/
theorem proto.codec.PlainPacketCodec.decode_resume (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8)
    (h : (frame self.seq_id.val p).length + tail.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r1 codec1 src1 dst1 =>
      r1 = .Ok false ∧
      ∀ src2 : proto.codec.buf_model.VecBuf, src2.val = src1.val ++ (frame self.seq_id.val p).drop k ++ tail →
        (proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut codec1 src2 dst1 max comp ⦃ r codec src' dst' =>
          r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
          codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄) ⦄ := by
  have hd0 : alloc.vec.Vec.length dst = 0 := by simp [alloc.vec.Vec.length, hdst]
  have hsl : alloc.vec.Vec.length src ≤ (frame self.seq_id.val p).length := by
    show src.val.length ≤ _; rw [hsrc]; simp
  apply WP.spec_mono (proto.codec.PlainPacketCodec.decode_spec self (by rw [hidle]; simp)
    src dst max comp (by omega))
  rintro ⟨r, codec, src1, dst1⟩ ⟨heq, hval⟩
  rw [hidle, hsrc, hdst] at heq
  simp only [ChunkState.of] at heq
  rcases hpd : plainDecode self.seq_id .idle ((frame self.seq_id.val p).take k) [] max.val comp with
    ⟨r0, seq1, st1, src1', dst1'⟩
  have hres := plainDecode_resume self.seq_id p tail k hk max.val hmax comp r0 seq1 st1 src1' dst1' hpd
  have hsz := plainDecodeAux_sizes (((frame self.seq_id.val p).take k).length + 1) self.seq_id .idle
    ((frame self.seq_id.val p).take k) [] max.val comp
  have hpd' : plainDecode self.seq_id .idle ((frame self.seq_id.val p).take k) [] max.val comp =
      plainDecodeAux (((frame self.seq_id.val p).take k).length + 1) self.seq_id .idle
        ((frame self.seq_id.val p).take k) [] max.val comp := rfl
  rw [← hpd', hpd] at hsz
  rw [hpd] at heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨h1, h2, h3, h4, h5⟩ := heq
  subst h1
  refine ⟨hres.1, ?_⟩
  intro src2 hsrc2
  have hlen2 : alloc.vec.Vec.length dst1 + alloc.vec.Vec.length src2 + 2 ^ 24 ≤ Usize.max := by
    have e1 : alloc.vec.Vec.length dst1 = dst1.val.length := rfl
    have e2 : alloc.vec.Vec.length src2 = src2.val.length := rfl
    rw [e1, e2, hsrc2, h4, h5]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_nil] at hsz ⊢
    omega
  have hv1 : ∀ seq needed, codec.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max := by
    intro seq needed hcd
    have hv' := hval (by rw [hidle]; trivial)
    rw [hcd] at hv'
    simp only [ChunkState.of, ChunkState.Valid] at hv'
    have hmax : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
    omega
  apply WP.spec_mono (proto.codec.PlainPacketCodec.decode_spec codec hv1 src2 dst1 max comp hlen2)
  rintro ⟨r', codec', src', dst'⟩ ⟨heq', _⟩
  have h3' : ChunkState.of codec.chunk_decoder = st1 := h3
  rw [h2, h3', hsrc2, h4, h5, hres.2] at heq'
  simp only [Prod.mk.injEq] at heq'
  obtain ⟨g1, g2, g3, g4, g5⟩ := heq'
  refine ⟨g1, g2, ?_, g4, g5⟩
  cases hcd : codec'.chunk_decoder <;> simp_all [ChunkState.of]

/-- Out of sync: an idle codec given (outside compressed mode) the chunks of a payload whose sequence id `s` is not the expected one fails with `PacketsOutOfSync`; its expected sequence id is unchanged and its chunk decoder is idle again (the first chunk has been consumed). Only the first chunk has to pass the size check (`hmax`). -/
theorem proto.codec.PlainPacketCodec.decode_out_of_sync (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (s : U8) (hs : s ≠ self.seq_id)
    (p tail : List U8) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame s.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : min p.length maxPayloadLen ≤ max.val) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max none ⦃ r codec _ _ =>
      r = .Err .PacketsOutOfSync ∧ codec.seq_id = self.seq_id ∧ codec.chunk_decoder = .Idle ⦄ := by
  have hd0 : alloc.vec.Vec.length dst = 0 := by simp [alloc.vec.Vec.length, hdst]
  apply WP.spec_mono (proto.codec.PlainPacketCodec.decode_spec self (by rw [hidle]; simp)
    src dst max none (by omega))
  rintro ⟨r, codec, src', dst'⟩ ⟨heq, _⟩
  rw [hidle, hsrc, hdst] at heq
  simp only [ChunkState.of] at heq
  have hos := plainDecode_outOfSync self.seq_id s hs p tail max.val hmax
  rcases hpd : plainDecode self.seq_id .idle (frame s.val p ++ tail) [] max.val none with ⟨r0, seq1, st1, src1, dst1⟩
  rw [hpd] at heq hos
  simp only [Prod.mk.injEq] at heq
  simp only at hos
  refine ⟨heq.1.trans hos.1, heq.2.1.trans hos.2.1, ?_⟩
  have h3 := heq.2.2.1.trans hos.2.2
  cases hcd : codec.chunk_decoder <;> simp_all [ChunkState.of]

end mysql_common
