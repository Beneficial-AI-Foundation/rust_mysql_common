import Defs

/-! Statements for `fn packet_to_chunks` (spec file: `Specs/Proto/Codec.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `packet_to_chunks(seq_id, packet, dst)`: consumes the whole packet and appends its chunks (`frame`: chunks of at most `2^24 - 1` bytes, each with a 3-byte length and the sequence id, starting at `seq_id` and wrapping; an empty last chunk iff the length is a multiple of `2^24 - 1`); returns the next sequence id. -/
theorem proto.codec.packet_to_chunks_spec (seq : U8) (packet dst : proto.codec.buf_model.VecBuf) (h : dst.length + (frame seq.val packet.val).length ≤ Usize.max) :
    proto.codec.packet_to_chunks proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq packet dst ⦃ seq' packet' dst' =>
      seq'.val = (seq.val + frameCount packet.length) % 256 ∧ packet'.val = [] ∧
      dst'.val = dst.val ++ frame seq.val packet.val ⦄ := by
  sorry

end mysql_common
