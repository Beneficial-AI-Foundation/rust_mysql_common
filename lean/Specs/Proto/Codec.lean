import Proofs.Proto.Codec.PacketToChunks
import Proofs.Proto.Codec.ChunkInfo
import Proofs.Proto.Codec.ChunkDecoder
import Proofs.Proto.Codec.PlainPacketCodec

/-!
# `src/proto/codec/mod.rs`
    The plain (uncompressed) packet codec: splitting a payload into chunks (`packet_to_chunks`),
    the incremental chunk reader (`ChunkDecoder`, `ChunkInfo`) and the packet codec
    (`PlainPacketCodec`: `encode`, `decode`, `reset_seq_id`).

    **Patch.** Translation patch 21 makes these functions generic over crate-local buffer traits
    (`buf_model::PacketBuf`, `PacketBufMut`, `Reserve`) instead of `bytes::Buf`/`BufMut`/`BytesMut`,
    with a crate-local `NonZeroUsize`. The statements are at the model buffer `buf_model::VecBuf` (a
    `Vec<u8>` with the semantics of `BytesMut`) for every buffer argument; the patch header argues
    that the crate's own instantiations (`BytesMut`, the caller's `Buf`/`BufMut`) behave the same.
    `ChunkInfo::seq_id` and `PlainPacketCodec` are crate-private; they are stated because the
    public `PacketCodec` is built on them.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Framing.lean` (`maxPayloadLen`, `frame`, `frameCount`,
    `ChunkState`, `ChunkState.of`, `ChunkState.Valid`, `chunkInfoSeq`, `chunkStep`, `plainDecode`),
    `Defs/Bytes.lean` (`byte`).

    **Reading the statements.** `&mut` arguments come back as components of the result: for
    `decode`, `(result, decoder or codec, src, dst)`. The size bounds on `dst` only rule out
    arithmetic overflow of `usize` lengths (no real buffer comes near them). A `ChunkDecoder` is
    assumed to be in a state the decoder can produce (`ChunkState.Valid`; the Rust enum's fields
    are public).

    **Not covered.** The compressed codec (`compress`, `CompDecoder`, `CompData`, `PacketCodec` with
    compression; uses `flate2`, out of scope), `PacketCodec` itself and its `Decoder`/`Encoder`
    impls (they use `BytesMut` directly), `buf_model` (the translation model).

    **Behaviour to note.**
    * `max_allowed_packet` is checked against `dst.len() + chunk length` when a chunk header is
      read, before the payload is there; an empty chunk is never checked.
    * A chunk is classified `Middle` iff the output length becomes a multiple of `2^24 - 1`:
      correct when `dst` holds only earlier chunks of the same packet (documented), wrong otherwise.
    * In compressed mode (`comp_seq_id = Some(c)`) a chunk with sequence id `c` is accepted in place
      of the expected one (`net_flush` resynchronisation).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `fn packet_to_chunks` -/

/-- `packet_to_chunks(seq_id, packet, dst)`: consumes the whole packet and appends its chunks (`frame`: chunks of at most `2^24 - 1` bytes, each with a 3-byte length and the sequence id, starting at `seq_id` and wrapping; an empty last chunk iff the length is a multiple of `2^24 - 1`); returns the next sequence id. -/
recall proto.codec.packet_to_chunks_spec (seq : U8) (packet dst : proto.codec.buf_model.VecBuf) (h : dst.length + (frame seq.val packet.val).length ≤ Usize.max) :
    proto.codec.packet_to_chunks proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq packet dst ⦃ seq' packet' dst' =>
      seq'.val = (seq.val + frameCount packet.length) % 256 ∧ packet'.val = [] ∧
      dst'.val = dst.val ++ frame seq.val packet.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.packet_to_chunks_spec`

/-! ### `enum ChunkInfo and its impls` -/

/-- `seq_id`: the sequence id of either variant. -/
recall proto.codec.ChunkInfo.seq_id_eq (ci : proto.codec.ChunkInfo) :
    proto.codec.ChunkInfo.seq_id ci = ok (chunkInfoSeq ci)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.ChunkInfo.seq_id_eq`

/-! ### `enum ChunkDecoder and its impls` -/

/-- `decode(src, dst, max_allowed_packet)`: total; exactly one step of `chunkStep` (needs more input, a chunk read, or `PacketTooLarge`), with the new state, input and output. -/
recall proto.codec.ChunkDecoder.decode_spec (self : proto.codec.ChunkDecoder) (hv : (ChunkState.of self).Valid) (src dst : proto.codec.buf_model.VecBuf)
    (max : Usize) (h : dst.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.ChunkDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, ChunkState.of cd, src'.val, dst'.val) = chunkStep (ChunkState.of self) src.val dst.val max.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.ChunkDecoder.decode_spec`

/-! ### `struct PlainPacketCodec and its impls` -/

/-- `reset_seq_id`: the sequence id becomes 0. -/
recall proto.codec.PlainPacketCodec.reset_seq_id_eq (self : proto.codec.PlainPacketCodec) :
    proto.codec.PlainPacketCodec.reset_seq_id self = ok { self with seq_id := 0#u8 }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.reset_seq_id_eq`

/-- `encode(packet, dst, max_allowed_packet)`: `PacketTooLarge`, nothing changed, if the packet is longer than `max_allowed_packet`; otherwise appends its chunks from the codec's sequence id (`frame`), consumes the packet, and advances the sequence id by the number of chunks. -/
recall proto.codec.PlainPacketCodec.encode_spec (self : proto.codec.PlainPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : dst.length + (frame self.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r codec packet' dst' =>
      if max.val < packet.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with seq_id := byte (self.seq_id.val + frameCount packet.length) } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame self.seq_id.val packet.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.encode_spec`

/-- `decode(src, dst, max_allowed_packet, comp_seq_id)`: total; exactly `plainDecode` (chunks read with `chunkStep` until the last chunk of a packet, `Ok(true)`, or more input is needed, `Ok(false)`, or an error: `PacketTooLarge`, or `PacketsOutOfSync` for a chunk whose sequence id is neither the expected one nor `comp_seq_id`). -/
recall proto.codec.PlainPacketCodec.decode_spec (self : proto.codec.PlainPacketCodec) (hv : (ChunkState.of self.chunk_decoder).Valid)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (comp : Option U8)
    (h : dst.length + src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_spec`

/-- Headline round trip: an idle codec decodes the chunks of a payload (`frame`, as `encode` writes them) starting at its sequence id into an empty `dst`: the whole payload, `Ok(true)`, the input after the chunks left, the sequence id advanced by the number of chunks, the decoder idle again. -/
recall proto.codec.PlainPacketCodec.decode_frame (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame self.seq_id.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
      codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_frame`

/-- Incremental decoding: on a strict prefix of the chunks of a payload, an idle codec reports that more input is needed (`Ok(false)`), never an error. -/
recall proto.codec.PlainPacketCodec.decode_prefix (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r _ _ _ =>
      r = .Ok false ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_prefix`

end mysql_common
