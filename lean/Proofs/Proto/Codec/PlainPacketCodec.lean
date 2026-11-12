import Defs

/-! Statements for `struct PlainPacketCodec and its impls` (spec file: `Specs/Proto/Codec.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `reset_seq_id`: the sequence id becomes 0. -/
theorem proto.codec.PlainPacketCodec.reset_seq_id_eq (self : proto.codec.PlainPacketCodec) :
    proto.codec.PlainPacketCodec.reset_seq_id self = ok { self with seq_id := 0#u8 } := by
  sorry

/-- `encode(packet, dst, max_allowed_packet)`: `PacketTooLarge`, nothing changed, if the packet is longer than `max_allowed_packet`; otherwise appends its chunks from the codec's sequence id (`frame`), consumes the packet, and advances the sequence id by the number of chunks. -/
theorem proto.codec.PlainPacketCodec.encode_spec (self : proto.codec.PlainPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : max.val < packet.length ∨ dst.length + (frame self.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r codec packet' dst' =>
      if max.val < packet.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with seq_id := byte (self.seq_id.val + frameCount packet.length) } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame self.seq_id.val packet.val ⦄ := by
  sorry

/-- `decode(src, dst, max_allowed_packet, comp_seq_id)`: total; exactly `plainDecode` (chunks read with `chunkStep` until the last chunk of a packet, `Ok(true)`, or more input is needed, `Ok(false)`, or an error: `PacketTooLarge`, or `PacketsOutOfSync` for a chunk whose sequence id is neither the expected one nor `comp_seq_id`); the new state is again valid. -/
theorem proto.codec.PlainPacketCodec.decode_spec (self : proto.codec.PlainPacketCodec) (hv : (ChunkState.of self.chunk_decoder).Valid)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (comp : Option U8)
    (h : dst.length + src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp ∧
      (ChunkState.of codec.chunk_decoder).Valid ⦄ := by
  sorry

/-- Headline round trip: an idle codec decodes the chunks of a payload (`frame`, as `encode` writes them) starting at its sequence id into an empty `dst`: the whole payload, `Ok(true)`, the input after the chunks left, the sequence id advanced by the number of chunks, the decoder idle again. -/
theorem proto.codec.PlainPacketCodec.decode_frame (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame self.seq_id.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
      codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄ := by
  sorry

/-- Incremental decoding: on a strict prefix of the chunks of a payload, an idle codec reports that more input is needed (`Ok(false)`), never an error; the state it leaves is `plainDecode`'s (see `decode_resume` for continuing). -/
theorem proto.codec.PlainPacketCodec.decode_prefix (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok false ∧
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id ChunkState.idle ((frame self.seq_id.val p).take k) [] max.val comp ⦄ := by
  sorry

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
  sorry

/-- Out of sync: an idle codec given (outside compressed mode) the chunks of a payload whose sequence id `s` is not the expected one fails with `PacketsOutOfSync`, and its expected sequence id is unchanged. -/
theorem proto.codec.PlainPacketCodec.decode_out_of_sync (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (s : U8) (hs : s ≠ self.seq_id)
    (p tail : List U8) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame s.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max none ⦃ r codec _ _ =>
      r = .Err .PacketsOutOfSync ∧ codec.seq_id = self.seq_id ⦄ := by
  sorry

end mysql_common
