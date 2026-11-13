import Defs

/-! Statements for `enum CompDecoder and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `decode(src, dst, max_allowed_packet)`: total. It is exactly one step of `compStep`, inflating with a new stream, and gives the new state, input and output. The step's outcome is one of: more input needed, a compressed packet read, `PacketTooLarge`, `BadCompressedPacketHeader`, or an `Io` error from inflating. The only hypothesis is that the lengths computed fit in a `usize` (`compStepFits`). From a valid state, the new state is again valid. -/
theorem proto.codec.CompDecoder.decode_spec (self : proto.codec.CompDecoder) (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : compStepFits (CompState.of self) dst.val) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList Trusted.decompressNew) (CompState.of self) src.val dst.val max.val ∧
      ((CompState.of self).Valid → (CompState.of cd).Valid) ⦄ := by
  sorry

/-- Round trip for one packet. An idle decoder reads a compressed packet in the form the crate writes it (`compPacket`: stored, or a successful deflate of the piece) back to the piece. The result is `Ok(Last(seq))`, exactly the packet is consumed, and the decoder is idle again. (This rests on `Trusted.inflate_deflate`.) -/
theorem proto.codec.CompDecoder.decode_compPacket (seq : U8) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = compPacket seq.val chunk zo ++ tail) (max : Usize)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val) (h : dst.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut .Idle src dst max ⦃ r cd src' dst' =>
      r = .Ok (some (.Last seq)) ∧ cd = .Idle ∧ src'.val = tail ∧ dst'.val = dst.val ++ chunk ⦄ := by
  sorry

end mysql_common
