import Defs
import Proofs.Util.ParseBuf
import Proofs.Proto.Codec.PacketCodecInner
import Proofs.Proto.Codec.PlainPacketCodec

/-! Statements for `struct PacketCodec and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `reset_seq_id`: the sequence id becomes 0 (for a compressed codec, both the compressed and the plain one). -/
theorem proto.codec.PacketCodec.reset_seq_id_eq (self : proto.codec.PacketCodec) :
    proto.codec.PacketCodec.reset_seq_id self = ok { self with inner := match self.inner with
      | .Plain c => .Plain { c with seq_id := 0#u8 }
      | .Comp c => .Comp { c with comp_seq_id := 0#u8, plain_codec := { c.plain_codec with seq_id := 0#u8 } } } := by
  simp only [proto.codec.PacketCodec.reset_seq_id, proto.codec.PacketCodecInner.reset_seq_id_eq, bind_ok]
  cases self.inner <;> rfl

/-- `sync_seq_id`: for a compressed codec with no decompressed input pending, the plain sequence id becomes the compressed one; otherwise nothing changes. -/
theorem proto.codec.PacketCodec.sync_seq_id_eq (self : proto.codec.PacketCodec) :
    proto.codec.PacketCodec.sync_seq_id self = ok { self with inner := match self.inner with
      | .Plain c => .Plain c
      | .Comp c => .Comp (if c.in_buf.val = [] then
          { c with plain_codec := { c.plain_codec with seq_id := c.comp_seq_id } } else c) } := by
  simp only [proto.codec.PacketCodec.sync_seq_id, proto.codec.PacketCodecInner.sync_seq_id_eq, bind_ok]
  cases self.inner <;> rfl

/-- `compress(level)`: `max_allowed_packet` is kept. On a plain codec, compression is turned on with compressed sequence id 0, empty buffers, an idle compressed-packet reader and no flate2 streams, and the plain codec (sequence id, chunk reader) is kept. On a compressed codec, a different level replaces the level and drops the deflate stream. Never panics, even for a level above 10 (see `compress_then_encode_panics`). -/
theorem proto.codec.PacketCodec.compress_spec (self : proto.codec.PacketCodec) (lvl : flate2.Compression) :
    proto.codec.PacketCodec.compress self lvl ⦃ r =>
      r.max_allowed_packet = self.max_allowed_packet ∧
      match self.inner with
      | .Plain c => ∃ cc, r.inner = .Comp cc ∧ cc.level = lvl ∧ cc.comp_seq_id = 0#u8 ∧ cc.in_buf.val = [] ∧
          cc.out_buf.val = [] ∧ cc.comp_decoder = .Idle ∧ cc.deflater = none ∧ cc.inflater = none ∧
          cc.plain_codec = c
      | .Comp c => r.inner = if c.level.level = lvl.level then .Comp c else .Comp { c with level := lvl, deflater := none } ⦄ := by
  unfold proto.codec.PacketCodec.compress
  have hs := proto.codec.PacketCodecInner.compress_spec self.inner lvl
  obtain ⟨v, hv, hp⟩ := PBUtil.spec_eq_ok hs
  rw [hv]
  simp only [bind_ok, WP.spec_ok, true_and]
  cases hi : self.inner <;> rw [hi] at hp <;> exact hp

/-- `decode(src, dst)` on a plain codec: total; exactly `plainDecode` with the codec's `max_allowed_packet` and no compressed sequence id (as `PlainPacketCodec.decode_spec`). -/
theorem proto.codec.PacketCodec.decode_plain_spec (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c)
    (hv : ∀ seq needed, c.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max)
    (src dst : proto.codec.buf_model.VecBuf) (h : dst.val.length + src.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst ⦃ r codec src' dst' =>
      codec.max_allowed_packet = self.max_allowed_packet ∧
      ∃ c', codec.inner = .Plain c' ∧
        (r, c'.seq_id, ChunkState.of c'.chunk_decoder, src'.val, dst'.val) =
          plainDecode c.seq_id (ChunkState.of c.chunk_decoder) src.val dst.val self.max_allowed_packet.val none ⦄ := by
  obtain ⟨⟨r, c', s', d'⟩, hv, hp, _⟩ := PBUtil.spec_eq_ok (proto.codec.PlainPacketCodec.decode_spec c hv src dst self.max_allowed_packet none h)
  simp [proto.codec.PacketCodec.decode, proto.codec.PacketCodecInner.decode_eq, hc, hv]
  exact hp

/-- `decode(src, dst)` on a compressed codec: the compressed codec's `decode` with the codec's `max_allowed_packet` (see the `CompPacketCodec.decode_*` statements). -/
theorem proto.codec.PacketCodec.decode_comp_eq (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (src dst : proto.codec.buf_model.VecBuf) :
    proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst =
      (do
        let (r, c', src', dst') ← proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst self.max_allowed_packet
        ok (r, { self with inner := .Comp c' }, src', dst')) := by
  simp only [proto.codec.PacketCodec.decode, proto.codec.PacketCodecInner.decode_eq, hc]
  simp only [Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨a, b, c, d⟩ := x
  simp

/-- `encode(src, dst)` on a plain codec: `PacketTooLarge` (nothing changed) if the packet is longer than `max_allowed_packet`; otherwise its chunks (`frame`) are appended to `dst`, the packet is consumed, and the sequence id advances by the number of chunks (as `PlainPacketCodec.encode_spec`). -/
theorem proto.codec.PacketCodec.encode_plain_spec (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c) (packet dst : proto.codec.buf_model.VecBuf)
    (h : self.max_allowed_packet.val < packet.val.length ∨ dst.val.length + (frame c.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst ⦃ r codec packet' dst' =>
      if self.max_allowed_packet.val < packet.val.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with inner := .Plain { c with seq_id := byte (c.seq_id.val + frameCount packet.val.length) } } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame c.seq_id.val packet.val ⦄ := by
  obtain ⟨v, hv, hp⟩ := PBUtil.spec_eq_ok (proto.codec.PlainPacketCodec.encode_spec c packet dst self.max_allowed_packet h)
  obtain ⟨r, c', packet', dst'⟩ := v
  simp [proto.codec.PacketCodec.encode, proto.codec.PacketCodecInner.encode_eq, hc, hv]
  have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
  rw [e0] at hp
  split_ifs at hp ⊢ with hm
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    subst h1 h2 h3 h4
    refine ⟨rfl, ?_, rfl, rfl⟩
    cases self; simp_all
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    subst h1 h2
    exact ⟨rfl, rfl, h3, h4⟩

/-- `encode(src, dst)` on a compressed codec: the compressed codec's `encode` with the codec's `max_allowed_packet` (see `CompPacketCodec.encode_spec` and its panics). -/
theorem proto.codec.PacketCodec.encode_comp_eq (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (packet dst : proto.codec.buf_model.VecBuf) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst =
      (do
        let (r, c', packet', dst') ← proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst self.max_allowed_packet
        ok (r, { self with inner := .Comp c' }, packet', dst')) := by
  simp only [proto.codec.PacketCodec.encode, proto.codec.PacketCodecInner.encode_eq, hc]
  simp only [Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨a, b, c, d⟩ := x
  simp

/-- Headline round trip, plain codecs. Suppose a plain codec encodes a packet successfully. A plain codec with the same sequence id, an idle chunk reader and at least the same `max_allowed_packet` then decodes the bytes written (followed by anything) back to exactly the packet. The result is `Ok(true)`, with the input after them left, both sequence ids equal, and the reader idle. -/
theorem proto.codec.PacketCodec.encode_decode_plain (enc dec : proto.codec.PacketCodec) (ce cd : proto.codec.PlainPacketCodec)
    (he : enc.inner = .Plain ce) (hd : dec.inner = .Plain cd) (hseq : cd.seq_id = ce.seq_id) (hidle : cd.chunk_decoder = .Idle)
    (hmax : enc.max_allowed_packet.val ≤ dec.max_allowed_packet.val)
    (packet dst : proto.codec.buf_model.VecBuf) (h : dst.val.length + (frame ce.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve enc packet dst ⦃ r enc' _ dst' =>
      r = .Ok () → ∃ ce', enc'.inner = .Plain ce' ∧
        ∀ (tail : List U8) (src d0 : proto.codec.buf_model.VecBuf), src.val = dst'.val.drop dst.val.length ++ tail → d0.val = [] →
          src.val.length + 2 ^ 24 ≤ Usize.max →
          proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut dec src d0 ⦃ r2 dec' src' d' =>
            r2 = .Ok true ∧ d'.val = packet.val ∧ src'.val = tail ∧
            ∃ cd', dec'.inner = .Plain cd' ∧ cd'.seq_id = ce'.seq_id ∧ cd'.chunk_decoder = .Idle ⦄ ⦄ := by
  obtain ⟨v, hv1, hp1⟩ := PBUtil.spec_eq_ok (proto.codec.PacketCodec.encode_plain_spec enc ce he packet dst (Or.inr h))
  rw [hv1]
  obtain ⟨r, enc', packet', dst'⟩ := v
  simp only [WP.spec_ok, WP.uncurry'_pair] at hp1 ⊢
  intro hr
  split_ifs at hp1 with hm
  · obtain ⟨h1, -⟩ := hp1
    rw [hr] at h1; cases h1
  · obtain ⟨-, h2, -, h4⟩ := hp1
    refine ⟨{ ce with seq_id := byte (ce.seq_id.val + frameCount packet.val.length) }, by rw [h2], ?_⟩
    intro tail src d0 hsrc hd0 hlen
    have hsrc' : src.val = frame cd.seq_id.val packet.val ++ tail := by
      rw [hsrc, h4, hseq]; simp
    obtain ⟨⟨r2, c2, s2, d2⟩, hw, hq⟩ := PBUtil.spec_eq_ok (proto.codec.PlainPacketCodec.decode_frame cd hidle packet.val tail src d0 hsrc' hd0
      dec.max_allowed_packet (by omega) none hlen)
    simp only [WP.uncurry'_pair] at hq
    obtain ⟨q1, q2, q3, q4, q5⟩ := hq
    simp [proto.codec.PacketCodec.decode, proto.codec.PacketCodecInner.decode_eq, hd, hw]
    refine ⟨q1, q5, q4, ?_, q3⟩
    rw [q2, hseq]

/-- Headline round trip, compressed codecs. Suppose a compressed codec with an empty output buffer encodes a packet successfully, without panicking (`max_allowed_packet ≠ 0`; level at most 10, a kept deflate stream, or no piece long enough to deflate). The bytes it wrote (followed by anything) go to a compressed codec that has nothing pending, starts at the same two sequence ids, and has at least the same `max_allowed_packet`. That codec decodes them back to exactly the packet: `Ok(true)`, with the input after them left. Its compressed sequence id then equals the encoder's, its plain sequence id is advanced by the number of chunks, and nothing is pending. (The encoder instead sets its plain sequence id to the compressed one, as the server does.) Deflated pieces are read back by `Trusted.inflate_deflate` (this follows from `CompPacketCodec.encode_spec`, `compEncoding_compStreamOf`, `chunksOf_spec` and `chunksOf_dropLast_length` (which give `decode_compStream`'s `hsize` and `hlast` with `rest = []`), and `decode_compStream`). -/
theorem proto.codec.PacketCodec.encode_decode_comp (enc dec : proto.codec.PacketCodec) (ce cd : proto.codec.CompPacketCodec)
    (he : enc.inner = .Comp ce) (hd : dec.inner = .Comp cd) (hout : ce.out_buf.val = [])
    (hfresh : cd.in_buf.val = [] ∧ cd.comp_decoder = .Idle ∧ cd.plain_codec.chunk_decoder = .Idle)
    (hseq : cd.comp_seq_id = ce.comp_seq_id ∧ cd.plain_codec.seq_id = ce.plain_codec.seq_id)
    (hmax0 : enc.max_allowed_packet.val ≠ 0) (hmax : enc.max_allowed_packet.val ≤ dec.max_allowed_packet.val)
    (packet dst : proto.codec.buf_model.VecBuf)
    (hlvl : ce.deflater ≠ none ∨ ce.level.level.val ≤ 10 ∨
      Nat.min (compChunkSize enc.max_allowed_packet.val) (frame ce.plain_codec.seq_id.val packet.val).length < minCompressLength)
    (h : dst.val.length + 8 * (frame ce.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve enc packet dst ⦃ r enc' _ dst' =>
      r = .Ok () → ∃ ce', enc'.inner = .Comp ce' ∧
        ∀ (tail : List U8) (src d0 : proto.codec.buf_model.VecBuf), src.val = dst'.val.drop dst.val.length ++ tail → d0.val = [] →
          2 ^ 25 * (src.val.length + 1) ≤ Usize.max →
          proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut dec src d0 ⦃ r2 dec' src' d' =>
            r2 = .Ok true ∧ d'.val = packet.val ∧ src'.val = tail ∧
            ∃ cd', dec'.inner = .Comp cd' ∧ cd'.comp_seq_id = ce'.comp_seq_id ∧
              cd'.plain_codec.seq_id = byte (ce.plain_codec.seq_id.val + frameCount packet.val.length) ∧
              cd'.in_buf.val = [] ∧ cd'.comp_decoder = .Idle ∧ cd'.plain_codec.chunk_decoder = .Idle ⦄ ⦄ := by
  sorry

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). A compressed codec with `max_allowed_packet = 0` panics when encoding an empty packet (`chunks(0)` in `compress_with`), instead of returning an error. -/
theorem proto.codec.PacketCodec.encode_comp_max_zero (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (hmax : self.max_allowed_packet.val = 0) (packet dst : proto.codec.buf_model.VecBuf)
    (hp : packet.val = []) (h : c.out_buf.val.length + 4 ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst = fail .panic := by
  sorry

/-- A compression level above 10 is accepted by `compress`, but the first `encode` that deflates then panics: one whose packet (within `max_allowed_packet`) has chunks making a first piece of at least `minCompressLength` bytes. This is flate2's `debug_assert!(level <= 10)` in `Compress::new` (`src/ffi/miniz_oxide.rs:153`): debug builds only, no panic in release. The default zlib backend, outside the verified configuration, instead panics above 9 in every profile. -/
theorem proto.codec.PacketCodec.compress_then_encode_panics (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c) (lvl : flate2.Compression) (hlvl : 10 < lvl.level.val)
    (packet dst : proto.codec.buf_model.VecBuf) (hp : packet.val.length ≤ self.max_allowed_packet.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize self.max_allowed_packet.val) (frame c.seq_id.val packet.val).length)
    (h : dst.val.length + 8 * (frame c.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.compress self lvl ⦃ c2 =>
      proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c2 packet dst = fail .panic ⦄ := by
  sorry

/-- `Default`: a plain codec with sequence id 0, an idle chunk reader and `max_allowed_packet` = `DEFAULT_MAX_ALLOWED_PACKET` = 4 MiB. -/
theorem proto.codec.PacketCodec.default_eq :
    proto.codec.PacketCodec.Insts.CoreDefaultDefault.default =
      ok { max_allowed_packet := 4194304#usize, inner := .Plain { seq_id := 0#u8, chunk_decoder := .Idle } } := by
  simp only [proto.codec.PacketCodec.Insts.CoreDefaultDefault.default, proto.codec.PacketCodecInner.default_eq,
    constants.DEFAULT_MAX_ALLOWED_PACKET]
  have h1 : (4#usize * 1024#usize : Result Usize) = ok 4096#usize := by
    have := UScalar.mul_spec (x := 4#usize) (y := 1024#usize) (by scalar_tac)
    obtain ⟨v, hv, hp⟩ := PBUtil.spec_eq_ok this
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; simp_all
  have h2 : (4096#usize * 1024#usize : Result Usize) = ok 4194304#usize := by
    have := UScalar.mul_spec (x := 4096#usize) (y := 1024#usize) (by scalar_tac)
    obtain ⟨v, hv, hp⟩ := PBUtil.spec_eq_ok this
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; simp_all
  simp [h1, h2]

end mysql_common
