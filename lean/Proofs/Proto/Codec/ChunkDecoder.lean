import Defs

/-! Statements for `enum ChunkDecoder and its impls` (spec file: `Specs/Proto/Codec.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `decode(src, dst, max_allowed_packet)`: total; exactly one step of `chunkStep` (needs more input, a chunk read, or `PacketTooLarge`), with the new state, input and output; the new state is again valid, so the next call's `hv` holds. -/
theorem proto.codec.ChunkDecoder.decode_spec (self : proto.codec.ChunkDecoder) (hv : (ChunkState.of self).Valid) (src dst : proto.codec.buf_model.VecBuf)
    (max : Usize) (h : dst.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.ChunkDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, ChunkState.of cd, src'.val, dst'.val) = chunkStep (ChunkState.of self) src.val dst.val max.val ∧
      (ChunkState.of cd).Valid ⦄ := by
  sorry

end mysql_common
