import Defs

/-! Statements for `enum PacketCodecInner and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `reset_seq_id`: the sequence id of the plain codec, or both sequence ids of the compressed codec, become 0. -/
theorem proto.codec.PacketCodecInner.reset_seq_id_eq (self : proto.codec.PacketCodecInner) :
    proto.codec.PacketCodecInner.reset_seq_id self = ok (match self with
      | .Plain c => .Plain { c with seq_id := 0#u8 }
      | .Comp c => .Comp { c with comp_seq_id := 0#u8, plain_codec := { c.plain_codec with seq_id := 0#u8 } }) := by
  sorry

/-- `sync_seq_id`: nothing for the plain codec. For the compressed codec, the plain sequence id becomes the compressed one if no decompressed input is pending. -/
theorem proto.codec.PacketCodecInner.sync_seq_id_eq (self : proto.codec.PacketCodecInner) :
    proto.codec.PacketCodecInner.sync_seq_id self = ok (match self with
      | .Plain c => .Plain c
      | .Comp c => .Comp (if c.in_buf.val = [] then
          { c with plain_codec := { c.plain_codec with seq_id := c.comp_seq_id } } else c)) := by
  sorry

/-- `compress(level)`. On a plain codec, compression is turned on: the compressed sequence id is 0, the buffers are empty, the compressed-packet reader is idle, there are no flate2 streams yet, and the plain codec (sequence id and chunk reader) is kept as it was. On a compressed codec, a different level replaces the level and drops the deflate stream, and the same level changes nothing. Never panics, even for a level above 10 (that panic comes at the first deflate, see `CompPacketCodec.encode_level_panic`). -/
theorem proto.codec.PacketCodecInner.compress_spec (self : proto.codec.PacketCodecInner) (lvl : flate2.Compression) :
    proto.codec.PacketCodecInner.compress self lvl ⦃ r =>
      match self with
      | .Plain c => ∃ cc, r = .Comp cc ∧ cc.level = lvl ∧ cc.comp_seq_id = 0#u8 ∧ cc.in_buf.val = [] ∧
          cc.out_buf.val = [] ∧ cc.comp_decoder = .Idle ∧ cc.deflater = none ∧ cc.inflater = none ∧
          cc.plain_codec = c
      | .Comp c => r = if c.level.level = lvl.level then .Comp c else .Comp { c with level := lvl, deflater := none } ⦄ := by
  sorry

/-- `decode(src, dst, max_allowed_packet)`: the plain codec's `decode` without a compressed sequence id, or the compressed codec's `decode`. -/
theorem proto.codec.PacketCodecInner.decode_eq (self : proto.codec.PacketCodecInner) (src dst : proto.codec.buf_model.VecBuf) (max : Usize) :
    proto.codec.PacketCodecInner.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max =
      (match self with
      | .Plain c => do
        let (r, c', src', dst') ← proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst max none
        ok (r, .Plain c', src', dst')
      | .Comp c => do
        let (r, c', src', dst') ← proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst max
        ok (r, .Comp c', src', dst')) := by
  sorry

/-- `encode(packet, dst, max_allowed_packet)`: the plain or the compressed codec's `encode`. -/
theorem proto.codec.PacketCodecInner.encode_eq (self : proto.codec.PacketCodecInner) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize) :
    proto.codec.PacketCodecInner.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max =
      (match self with
      | .Plain c => do
        let (r, c', packet', dst') ← proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst max
        ok (r, .Plain c', packet', dst')
      | .Comp c => do
        let (r, c', packet', dst') ← proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst max
        ok (r, .Comp c', packet', dst')) := by
  sorry

/-- `Default`: a plain codec with sequence id 0 and an idle chunk reader. -/
theorem proto.codec.PacketCodecInner.default_eq :
    proto.codec.PacketCodecInner.Insts.CoreDefaultDefault.default =
      ok (.Plain { seq_id := 0#u8, chunk_decoder := .Idle }) := by
  sorry

end mysql_common
