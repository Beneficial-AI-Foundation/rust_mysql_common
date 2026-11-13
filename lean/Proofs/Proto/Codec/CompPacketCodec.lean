import Defs

/-! Statements for `struct CompPacketCodec and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `reset_seq_id`: both the compressed and the plain sequence ids become 0. -/
theorem proto.codec.CompPacketCodec.reset_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.reset_seq_id self =
      ok { self with comp_seq_id := 0#u8, plain_codec := { self.plain_codec with seq_id := 0#u8 } } := by
  sorry

/-- `sync_seq_id`: if no decompressed input is pending (`in_buf` empty, i.e. on a compressed-packet boundary), the plain sequence id becomes the compressed one; otherwise nothing changes. -/
theorem proto.codec.CompPacketCodec.sync_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.sync_seq_id self =
      ok (if self.in_buf.val = [] then
            { self with plain_codec := { self.plain_codec with seq_id := self.comp_seq_id } }
          else self) := by
  sorry

/-- `decode(src, dst, max_allowed_packet)`: total. It never panics, and states the decoder can produce stay valid. It decodes compressed packets from `src` into the internal buffer `in_buf`, and plain packets from `in_buf` into `dst` (see the round-trip, streaming and error statements below).
    The hypotheses: the pending states are valid (`CompState.Valid`, `ChunkState.Valid`; the decoder only produces valid states, but the enum fields are public), and a size bound that rules out `usize` overflow. That bound is stronger than necessary: each compressed packet of at least 7 input bytes can add up to `2^24` bytes to `in_buf`. -/
theorem proto.codec.CompPacketCodec.decode_total (self : proto.codec.CompPacketCodec)
    (hc : (CompState.of self.comp_decoder).Valid) (hp : (ChunkState.of self.plain_codec.chunk_decoder).Valid)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : 2 ^ 25 * (self.in_buf.val.length + src.val.length + dst.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ _ c' _ _ =>
      (CompState.of c'.comp_decoder).Valid ∧ (ChunkState.of c'.plain_codec.chunk_decoder).Valid ⦄ := by
  sorry

/-- Pipelined plain packets. Take a decoder whose chunk reader is idle and whose decompressed buffer `in_buf` starts with the chunks of a payload `p` (`frame`, from the plain sequence id), followed by anything (`rest`, e.g. the next packet). It returns `Ok(true)` with exactly `p` in `dst`, leaving `rest` in `in_buf`. It reads nothing from `src`. The compressed reader and sequence id, `out_buf`, both flate2 streams and the level are unchanged, and the plain sequence id is advanced by the number of chunks. -/
theorem proto.codec.CompPacketCodec.decode_buffered (self : proto.codec.CompPacketCodec)
    (hidle : self.plain_codec.chunk_decoder = .Idle) (p rest : List U8)
    (hin : self.in_buf.val = frame self.plain_codec.seq_id.val p ++ rest)
    (src dst : proto.codec.buf_model.VecBuf) (hdst : dst.val = []) (max : Usize) (hmax : p.length ≤ max.val)
    (h : self.in_buf.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ c'.in_buf.val = rest ∧ src' = src ∧
      c'.comp_seq_id = self.comp_seq_id ∧ c'.comp_decoder = self.comp_decoder ∧
      c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
      c'.plain_codec.chunk_decoder = .Idle ∧ c'.out_buf = self.out_buf ∧ c'.deflater = self.deflater ∧
      c'.inflater = self.inflater ∧ c'.level = self.level ⦄ := by
  sorry

/-- Headline round trip (decoding). Take a decoder with nothing pending (`in_buf` empty, both readers idle). Feed it any compressed stream (`CompStreamOf`) whose pieces carry the chunks of a payload `p` followed by `rest`, then anything (`tail`). The chunks are `frame`, from the decoder's plain sequence id; the packets' sequence ids start at the decoder's compressed one.
    The pieces may be cut anywhere (non-empty, at most `min(2^24 - 1, max_allowed_packet)` bytes), each stored or deflated by flate2. The payload's chunks must end in the last piece, so `rest` is the start of what comes next.
    The decoder gives back exactly `p` with `Ok(true)`: the whole stream is consumed (`tail` left), and `rest` stays in `in_buf`. The compressed sequence id is advanced by the number of packets, the plain one by the number of chunks, and both readers are idle.
    Deflated pieces are read back by `Trusted.inflate_deflate`, with any inflate stream. A deflated piece is covered only when it is flate2/miniz_oxide's own output; a server's zlib stream is covered only by `decode_total` and the error statements. -/
theorem proto.codec.CompPacketCodec.decode_compStream (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest tail out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out ++ tail) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (src.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧ c'.in_buf.val = rest ∧
      c'.comp_seq_id = byte (self.comp_seq_id.val + pieces.length) ∧
      c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
      c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄ := by
  sorry

/-- Streaming. On a strict prefix of such a compressed stream (as in `decode_compStream`), a decoder with nothing pending reports that more input is needed (`Ok(false)`), never an error. Plain chunks completed so far may already be in `dst`. -/
theorem proto.codec.CompPacketCodec.decode_prefix (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (out.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r _ _ _ =>
      r = .Ok false ⦄ := by
  sorry

/-- Resumption. Decode a strict prefix of such a compressed stream (`Ok(false)`). Then call `decode` again with the returned codec and output, on what the first call left of the input followed by the rest of the stream (and anything after). This completes the packet exactly as in `decode_compStream`. -/
theorem proto.codec.CompPacketCodec.decode_resume (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest tail out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (out.length + tail.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r1 c1 src1 dst1 =>
      r1 = .Ok false ∧
      ∀ src2 : proto.codec.buf_model.VecBuf, src2.val = src1.val ++ out.drop k ++ tail →
        (proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c1 src2 dst1 max ⦃ r c' src' dst' =>
          r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧ c'.in_buf.val = rest ∧
          c'.comp_seq_id = byte (self.comp_seq_id.val + pieces.length) ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
          c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄) ⦄ := by
  sorry

/-- Out of sync. A decoder with nothing pending, given a compressed packet (as the crate writes them) whose sequence id `s` is not the expected one, fails with `PacketsOutOfSync`; the compressed sequence id is unchanged. **Quirk:** the packet has been consumed, and its plain bytes have been kept in `in_buf`, so a later call would decode them. -/
theorem proto.codec.CompPacketCodec.decode_out_of_sync (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (s : U8) (hs : s ≠ self.comp_seq_id) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = compPacket s.val chunk zo ++ tail)
    (max : Usize) (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val)
    (h : dst.val.length + 2 ^ 25 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketsOutOfSync ∧ c'.comp_seq_id = self.comp_seq_id ∧ c'.comp_decoder = .Idle ∧
      c'.in_buf.val = chunk ∧ src'.val = tail ∧ dst' = dst ⦄ := by
  sorry

/-- A compressed-packet header with a length above `max_allowed_packet` (either length), seen with nothing pending: `PacketTooLarge`, and nothing changes (the codec, input and output are as before). -/
theorem proto.codec.CompPacketCodec.decode_too_large (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hbig : max.val < Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketTooLarge ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄ := by
  sorry

/-- A compressed-packet header with compressed length 0 but a non-zero uncompressed length, within `max_allowed_packet`, seen with nothing pending: `BadCompressedPacketHeader`, and nothing changes. -/
theorem proto.codec.CompPacketCodec.decode_bad_header (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hcl : (compHeaderRead src.val).1 = 0) (hpl : (compHeaderRead src.val).2.2 ≠ 0)
    (hmax : (compHeaderRead src.val).2.2 ≤ max.val) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .BadCompressedPacketHeader ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄ := by
  sorry

/-- Inflate failure. A whole compressed packet (non-zero lengths within `max_allowed_packet`) whose payload the decoder's inflate stream fails to inflate to the declared length, seen with nothing pending, gives `Err(Io(e))` with flate2's error. **Quirk:** the 7 header bytes have been consumed, but the packet reader stays in the pending state of that header. A later call would therefore read the payload's bytes as if a header still preceded them, unless the codec is discarded (as callers do after an error). -/
theorem proto.codec.CompPacketCodec.decode_inflate_error (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (e : core.io.error.Error)
    (h7 : 7 + (compHeaderRead src.val).1 ≤ src.val.length)
    (hcl : (compHeaderRead src.val).1 ≠ 0) (hpl : (compHeaderRead src.val).2.2 ≠ 0)
    (hmax : Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2 ≤ max.val)
    (hinf : inflateList (self.inflater.getD Trusted.decompressNew)
      ((src.val.drop 7).take (compHeaderRead src.val).1) (compHeaderRead src.val).2.2 = .Err e)
    (h : 2 ^ 25 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err (.Io e) ∧ c'.comp_seq_id = self.comp_seq_id ∧ c'.in_buf.val = [] ∧
      CompState.of c'.comp_decoder =
        .packet (compHeaderRead src.val).2.1 (compHeaderRead src.val).1 (some (compHeaderRead src.val).2.2) ∧
      src'.val = src.val.drop 7 ∧ dst' = dst ⦄ := by
  sorry

/-- `encode(packet, dst, max_allowed_packet)`, whenever it does not panic (`max_allowed_packet ≠ 0` or the packet is too large; level at most 10, a kept deflate stream, or no piece long enough to deflate).
    * `PacketTooLarge` if the packet is longer than `max_allowed_packet`; nothing changes.
    * Otherwise the packet's chunks (`frame`, from the plain sequence id) are appended to `out_buf`, and `out_buf` is compressed into `dst` (`CompEncoding`, from the compressed sequence id; see `compress_with_spec`). The packet is consumed.
      - On `Ok`: `out_buf` is emptied, the compressed sequence id is advanced by the number of compressed packets, and the plain sequence id is set to it (synchronised as in the server's `net_serv.cc`).
      - On `Err`: deflating failed (an `Io` error). **Quirk:** the plain sequence id has already advanced but the compressed one has not. The pieces before the failure are already in `dst` as compressed packets, and also still in `out_buf`. So the next `encode` sends them a second time, with the same compressed sequence ids.
    The reading side (`in_buf`, the readers, the inflate stream) and the level are untouched. The deflate stream is not described. -/
theorem proto.codec.CompPacketCodec.encode_spec (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (hmax : max.val ≠ 0 ∨ max.val < packet.val.length)
    (hlvl : self.deflater ≠ none ∨ self.level.level.val ≤ 10 ∨
      Nat.min (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length < minCompressLength)
    (h : self.out_buf.val.length + (frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max ∧
      dst.val.length + 8 * (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r c' packet' dst' =>
      if max.val < packet.val.length then
        r = .Err .PacketTooLarge ∧ c' = self ∧ packet' = packet ∧ dst' = dst
      else
        packet'.val = [] ∧ c'.level = self.level ∧ c'.in_buf = self.in_buf ∧
        c'.comp_decoder = self.comp_decoder ∧ c'.inflater = self.inflater ∧
        c'.plain_codec.chunk_decoder = self.plain_codec.chunk_decoder ∧
        match r with
        | .Ok _ =>
          c'.comp_seq_id = byte (self.comp_seq_id.val +
            (chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).length) ∧
          c'.plain_codec.seq_id = c'.comp_seq_id ∧ c'.out_buf.val = [] ∧
          ∃ out, CompEncoding (self.deflater.getD (Trusted.compressNew self.level)) self.level.level.val (compChunkSize max.val) self.comp_seq_id.val
              (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val) out ∧
            dst'.val = dst.val ++ out
        | .Err e =>
          (∃ ioe, e = .Io ioe) ∧ c'.comp_seq_id = self.comp_seq_id ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount packet.val.length) ∧
          c'.out_buf.val = self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val ∧
          ∃ k out, k < (chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).length ∧
            self.level.level.val ≠ 0 ∧
            minCompressLength ≤ ((chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).getD k []).length ∧
            CompPacketsOf (self.deflater.getD (Trusted.compressNew self.level)) self.level.level.val self.comp_seq_id.val
              ((chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).take k) out ∧
            dst'.val = dst.val ++ out ⦄ := by
  sorry

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). With `max_allowed_packet = 0`, encoding an empty packet panics. The empty packet passes the size check, its one empty chunk (4 bytes) goes to `out_buf`, and compressing it calls `chunks(0)`. (A non-empty packet gets `PacketTooLarge` instead.) -/
theorem proto.codec.CompPacketCodec.encode_max_zero (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf)
    (hp : packet.val = []) (h : self.out_buf.val.length + 4 ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst 0#usize = fail .panic := by
  sorry

/-- With no deflate stream yet and a level above 10, `encode` of a packet within `max_allowed_packet` panics when the first piece of `out_buf` (after the packet's chunks are added) has at least `minCompressLength` bytes. This is flate2's `debug_assert!(level <= 10)` in `Compress::new` (`src/ffi/miniz_oxide.rs:153`): debug builds only, no panic in release. -/
theorem proto.codec.CompPacketCodec.encode_level_panic (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (hd : self.deflater = none) (hlvl : 10 < self.level.level.val) (hp : packet.val.length ≤ max.val)
    (hbig : minCompressLength ≤
      Nat.min (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length)
    (h : self.out_buf.val.length + (frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max ∧
      dst.val.length + 8 * (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max = fail .panic := by
  sorry

end mysql_common
