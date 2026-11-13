import Proofs.Proto.Codec.PacketToChunks
import Proofs.Proto.Codec.ChunkInfo
import Proofs.Proto.Codec.ChunkDecoder
import Proofs.Proto.Codec.PlainPacketCodec
import Proofs.Proto.Codec.Compress
import Proofs.Proto.Codec.CompressWith
import Proofs.Proto.Codec.CompData
import Proofs.Proto.Codec.CompDecoder
import Proofs.Proto.Codec.PacketCodec
import Proofs.Proto.Codec.PacketCodecInner
import Proofs.Proto.Codec.CompPacketCodec

/-!
# `src/proto/codec/mod.rs`
    The packet codecs.
    * Plain (uncompressed): splitting a payload into chunks (`packet_to_chunks`), the incremental
      chunk reader (`ChunkDecoder`, `ChunkInfo`) and the packet codec (`PlainPacketCodec`).
    * Compressed: `compress`/`compress_with` (cutting the plain chunk stream into compressed
      packets), the compressed-packet reader (`CompData`, `CompDecoder`), and the compressed
      codec (`CompPacketCodec`).
    * The public codec `PacketCodec` (`default`, `reset_seq_id`, `sync_seq_id`,
      `compress(level)`, `decode`, `encode`) and its two variants (`PacketCodecInner`).
    The headline statements:
    * the round trips `PacketCodec.encode_decode_plain`/`_comp` (decode ∘ encode is the identity
      when the two codecs start at the same sequence ids);
    * `CompPacketCodec.decode_compEncoding`/`_prefix`/`_resume` (decoding any compressed stream
      of a payload's chunks, also incrementally);
    * the exact error cases of compressed decoding;
    * the panics.
    The `_spec`/`_eq` statements are exact or total.

    **Patches.** Translation patch 21 makes the plain codec generic over crate-local buffer traits
    (`buf_model::PacketBuf`, `PacketBufMut`, `Reserve`) instead of `bytes::Buf`/`BufMut`/`BytesMut`,
    with a crate-local `NonZeroUsize`; patch 123 does the same for the compressed codec and
    `PacketCodec` (adding `Clear`, and making `CompPacketCodec`'s own buffers `VecBuf`). The
    statements are at the model buffer `buf_model::VecBuf` (a `Vec<u8>` with the semantics of
    `BytesMut`) for every buffer argument; the patch headers argue that the crate's own
    instantiations (`BytesMut`, the caller's `Buf`/`BufMut`) behave the same. Patches 120/121 route
    every flate2 operation through the opaque module `proto::codec::trusted`; patch 122 turns
    `chunks(n)` into an index loop with the same `assert!(n != 0)`; patch 124 is `mem::take` as
    `mem::replace`. `ChunkInfo::seq_id`, `compress_with`, `CompData`'s methods,
    `PlainPacketCodec`, `CompPacketCodec` and `PacketCodecInner` are crate-private; they are
    stated because the public `PacketCodec` is built on them.

    **Configuration.** As in `Specs/Io.lean`. In particular flate2 uses its `rust_backend`
    (miniz_oxide), and the proofs use debug semantics: miniz_oxide's
    `debug_assert!(level <= 10)` is a panic (the default zlib backend, not verified, panics above
    9 in every profile).

    **Definitions used.** `Defs/Framing.lean` (`maxPayloadLen`, `frame`, `frameCount`,
    `ChunkState`, `ChunkState.of`, `ChunkState.Valid`, `chunkStepFits`, `chunkInfoSeq`, `chunkStep`,
    `plainDecode`),
    `Defs/Compression.lean` (`minCompressLength`, `compHeader`, `compHeaderRead`, `compPacket`,
    `compPackets`, `chunksOf`, `compChunkSize`, `Deflates`, `CompChoice`, `CompPacketsOf`,
    `CompEncoding`, `inflateList`, `CompState`, `CompState.of`, `CompState.Valid`, `compStep`,
    `compStepFits`),
    `Defs/Bytes.lean` (`byte`). Facts about these: `Specs/DefsCF.lean`, `Specs/DefsComp.lean`.

    **Trusted axioms.** The plain-codec statements rest on none of ours beyond `core.io.error.Error`
    (an opaque type). The compressed ones rest on the flate2 boundary of `FunsExternal.lean`:
    * the opaque streams and results: `Trusted.compressNew`, `decompressNew`, `deflateResult`,
      `deflateState`, `inflateResult`, `inflateState`, `vecCapacity`;
    * `Trusted.deflateResult_short` and `Trusted.inflateResult_len` (encode bounds);
    * `Trusted.inflate_deflate`, used by every round trip and by `decode_compPacket`,
      `decode_out_of_sync`, `decode_compEncoding`/`_prefix`/`_resume` and `encode_decode_comp`.
    These axioms only say what deflate and inflate do when they succeed, so the encode statements
    allow a deflate failure (`Err(Io)`), and the decode statements for arbitrary input are total,
    not exact, except `CompDecoder.decode_spec` and `decode_inflate_error`, which are exact in
    terms of flate2's (opaque) result. `Trusted.vecCapacity` (the shrink-on-threshold logic) is
    harmless: both branches leave an empty buffer. The deflate stream kept by a codec is never
    described.

    **Reading the statements.** `&mut` arguments come back as components of the result: for
    `decode`, `(result, decoder or codec, src, dst)`. The size bounds on `dst` only rule out
    arithmetic overflow of `usize` lengths (no real buffer comes near them). A `ChunkDecoder` is
    not assumed to be in a state the decoder can produce (`ChunkState.Valid`; the Rust enum's
    fields are public): the `decode` statements only ask that the lengths computed from it fit in a
    `usize`, and say that a valid state stays valid.

    **Not covered.**
    * Callers outside the crate: the public signatures are the patched ones.
    * `u24_le_bytes`, which the patch adds.
    * `CompDecoder::decode_with` (private; reached through `CompDecoder.decode_spec`, a fresh
      inflate stream, and the `CompPacketCodec.decode_*` statements).
    * An exact model of `CompPacketCodec::decode` on arbitrary input: its result depends on the
      opaque inflate streams the codec threads through. It is stated as total, plus the round-trip,
      streaming and error cases.
    * Memory use: the capacity-based shrinking of `in_buf`/`out_buf`.
    * `buf_model` (the translation model).

    **Behaviour to note.**
    * `max_allowed_packet` is checked against `dst.len() + chunk length` when a chunk header is
      read, before the payload is there; an empty chunk is never checked.
    * A chunk is classified `Middle` iff the output length becomes a multiple of `2^24 - 1`:
      correct when `dst` holds only earlier chunks of the same packet (documented), wrong otherwise.
    * In compressed mode (`comp_seq_id = Some(c)`) a chunk with sequence id `c` is accepted in place
      of the expected one (`net_flush` resynchronisation).
    * Compression: the stream of plain chunks is cut into pieces of
      `min(2^24 - 1, max_allowed_packet)` bytes. A piece is deflated only at a non-zero level, when
      it has at least 512 bytes (`MIN_COMPRESS_LENGTH`; the server uses 50), and when deflating
      makes it shorter; otherwise it is stored.
    * The compressed reader checks `max(compressed length, uncompressed length)` against
      `max_allowed_packet` (before `BadCompressedPacketHeader`). Plain chunks inside are checked
      again by the plain reader.
    * Bugs and quirks:
      - **Upstream bug:** `max_allowed_packet = 0` panics in `compress` on non-empty input, and in
        a compressed codec's `encode` of an empty packet (`chunks(0)`).
      - A compression level above 10 is accepted by `PacketCodec::compress` but panics at the
        first deflate (flate2 miniz_oxide `debug_assert!`).
      - `compress` on an empty `src` returns sequence id 0, not `seq_id`.
      - After a failed deflate, `encode` leaves the chunks in `out_buf` (they are re-sent by the
        next `encode`), with the plain sequence id advanced but the compressed one not.
      - After a failed inflate, the compressed reader has consumed the header but stays pending.
      - An out-of-sync compressed packet's data is kept in `in_buf`.
    * After `encode`, the compressed codec sets the plain sequence id to the compressed one
      (`net_serv.cc`); after `decode` it does not (`sync_seq_id` does that on request).
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

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.packet_to_chunks_spec
/-! ### `fn compress` -/

/-- `compress(seq_id, compression, max_allowed_packet, src, dst)` on an empty `src`: `Ok(0)`, nothing changed. **Quirk:** the result is `0`, not the given `seq_id` (upstream returns early with `Ok(0)`). The crate's own codec never calls it with an empty buffer. -/
recall proto.codec.compress_empty (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = []) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst = ok (.Ok 0#u8, src, dst)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_empty`
/-- **Upstream bug:** `compress` with `max_allowed_packet = 0` on a non-empty `src` panics (`src.chunks(0)`; the patched copy has the same `assert!`) instead of returning an error. -/
recall proto.codec.compress_max_zero (seq : U8) (lvl : flate2.Compression) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val ≠ []) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl 0#usize src dst = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_max_zero`
/-- `compress` at a compression level above 10 panics as soon as it deflates, i.e. when the first piece has at least `minCompressLength` bytes. flate2's miniz_oxide backend has `debug_assert!(level <= 10)` in `Compress::new`; the proofs use debug semantics (see the module docstring). -/
recall proto.codec.compress_level_panic (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0) (hlvl : 10 < lvl.level.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize max.val) src.val.length) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_level_panic`
/-- `compress(seq_id, compression, max_allowed_packet, src, dst)` on a non-empty `src`, whenever it does not panic (`max_allowed_packet ≠ 0`, and a level of at most 10 or no piece long enough to deflate). `src` is cut into pieces of `min(2^24 - 1, max_allowed_packet)` bytes (`chunksOf`, `compChunkSize`). Each piece is sent as one compressed packet (`CompEncoding`), with sequence ids counting up from `seq_id`. A piece is stored, or deflated when the level is not 0, the piece has at least 512 bytes and deflating made it shorter.
    * `Ok(s)`: `s` is `seq_id` plus the number of packets (mod 256), `src` is emptied, and the packets are appended to `dst`.
    * `Err(e)`: only when deflating a piece failed. Then `e` is an `Io` error, the level is not 0, and that piece has at least 512 bytes. `src` is unchanged, and `dst` has the packets of the pieces before it.
    The size bound only rules out `usize` overflow. -/
recall proto.codec.compress_spec (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0)
    (hlvl : lvl.level.val ≤ 10 ∨ Nat.min (compChunkSize max.val) src.val.length < minCompressLength)
    (h : dst.val.length + 8 * src.val.length ≤ Usize.max) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst ⦃ r src' dst' =>
      match r with
      | .Ok s =>
        s = byte (seq.val + (chunksOf (compChunkSize max.val) src.val).length) ∧ src'.val = [] ∧
        ∃ out, CompEncoding lvl.level.val (compChunkSize max.val) seq.val src.val out ∧ dst'.val = dst.val ++ out
      | .Err e =>
        (∃ ioe, e = .Io ioe) ∧ src' = src ∧
        ∃ k out, k < (chunksOf (compChunkSize max.val) src.val).length ∧ lvl.level.val ≠ 0 ∧
          minCompressLength ≤ ((chunksOf (compChunkSize max.val) src.val).getD k []).length ∧
          CompPacketsOf lvl.level.val seq.val ((chunksOf (compChunkSize max.val) src.val).take k) out ∧
          dst'.val = dst.val ++ out ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_spec`
/-! ### `fn compress_with` -/

/-- `compress_with(.., deflater, ..)` on an empty `src`: `Ok(0)`, nothing changed (the same quirk as `compress`). -/
recall proto.codec.compress_with_empty (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d max src dst = ok (.Ok 0#u8, d, src, dst)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_with_empty`
/-- **Upstream bug:** `compress_with` with `max_allowed_packet = 0` on a non-empty `src` panics (`chunks(0)`). -/
recall proto.codec.compress_with_max_zero (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val ≠ []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d 0#usize src dst = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_with_max_zero`
/-- `compress_with` with no deflate stream yet and a level above 10 panics when it creates one, i.e. when the first piece has at least `minCompressLength` bytes (the `debug_assert!` in `Compress::new`). -/
recall proto.codec.compress_with_level_panic (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0) (hlvl : 10 < lvl.level.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize max.val) src.val.length) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl none max src dst = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_with_level_panic`
/-- `compress_with(seq_id, compression, deflater, max_allowed_packet, src, dst)` on a non-empty `src`, whenever it does not panic: as `compress_spec`. A kept deflate stream is reused and never re-created, so the level is then not checked. The new stream is not described (it is opaque flate2 state). -/
recall proto.codec.compress_with_spec (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0)
    (hlvl : d ≠ none ∨ lvl.level.val ≤ 10 ∨ Nat.min (compChunkSize max.val) src.val.length < minCompressLength)
    (h : dst.val.length + 8 * src.val.length ≤ Usize.max) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d max src dst ⦃ r _ src' dst' =>
      match r with
      | .Ok s =>
        s = byte (seq.val + (chunksOf (compChunkSize max.val) src.val).length) ∧ src'.val = [] ∧
        ∃ out, CompEncoding lvl.level.val (compChunkSize max.val) seq.val src.val out ∧ dst'.val = dst.val ++ out
      | .Err e =>
        (∃ ioe, e = .Io ioe) ∧ src' = src ∧
        ∃ k out, k < (chunksOf (compChunkSize max.val) src.val).length ∧ lvl.level.val ≠ 0 ∧
          minCompressLength ≤ ((chunksOf (compChunkSize max.val) src.val).getD k []).length ∧
          CompPacketsOf lvl.level.val seq.val ((chunksOf (compChunkSize max.val) src.val).take k) out ∧
          dst'.val = dst.val ++ out ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.compress_with_spec`
/-! ### `enum ChunkInfo and its impls` -/

/-- `seq_id`: the sequence id of either variant. -/
recall proto.codec.ChunkInfo.seq_id_eq (ci : proto.codec.ChunkInfo) :
    proto.codec.ChunkInfo.seq_id ci = ok (chunkInfoSeq ci)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.ChunkInfo.seq_id_eq
/-! ### `enum ChunkDecoder and its impls` -/

/-- `decode(src, dst, max_allowed_packet)`: total; exactly one step of `chunkStep` (needs more input, a chunk read, or `PacketTooLarge`), with the new state, input and output. The only hypothesis is that the lengths computed fit in a `usize` (`chunkStepFits`; a valid state with `dst.length + 2^24 ≤ usize::MAX` is enough, `chunkStepFits_of_valid`). From a valid state the new state is again valid. -/
recall proto.codec.ChunkDecoder.decode_spec (self : proto.codec.ChunkDecoder) (src dst : proto.codec.buf_model.VecBuf)
    (max : Usize) (h : chunkStepFits (ChunkState.of self) src.val dst.val) :
    proto.codec.ChunkDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, ChunkState.of cd, src'.val, dst'.val) = chunkStep (ChunkState.of self) src.val dst.val max.val ∧
      ((ChunkState.of self).Valid → (ChunkState.of cd).Valid) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.ChunkDecoder.decode_spec
/-! ### `enum CompData and its impls` -/

/-- `CompData::new(compressed_len, uncompressed_len, max_allowed_packet)`:
    * `PacketTooLarge` if either length exceeds `max_allowed_packet` (this is checked first);
    * otherwise, with compressed length 0: `None` (an empty packet) if the uncompressed length is also 0, and `BadCompressedPacketHeader` if not;
    * otherwise `Uncompressed` (stored) if the uncompressed length is 0, and `Compressed` if not. -/
recall proto.codec.CompData.new_eq (cl pl max : Usize) :
    proto.codec.CompData.new cl pl max = ok
      (if max.val < Nat.max cl.val pl.val then .Err .PacketTooLarge
       else if cl.val = 0 then (if pl.val = 0 then .Ok none else .Err .BadCompressedPacketHeader)
       else .Ok (some (if pl.val = 0 then .Uncompressed cl else .Compressed cl pl)))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompData.new_eq`
/-- `needed`: the compressed length of either variant. -/
recall proto.codec.CompData.needed_eq (d : proto.codec.CompData) :
    proto.codec.CompData.needed d = ok (match d with | .Compressed n _ => n | .Uncompressed n => n)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompData.needed_eq`
/-- `write_payload(payload, dst, inflater)`. A stored payload is appended to `dst` as is. A compressed one is inflated to its uncompressed length with the kept stream (or a new one); on success the result is appended to `dst`, and on failure the error is returned and `dst` is unchanged. The stream is kept in both cases. -/
recall proto.codec.CompData.write_payload_spec (self : proto.codec.CompData) (payload : Slice U8) (dst : proto.codec.buf_model.VecBuf)
    (inf : Option flate2.mem.Decompress)
    (h : match self with
      | .Uncompressed _ => dst.val.length + payload.val.length ≤ Usize.max
      | .Compressed _ p => dst.val.length + p.val ≤ Usize.max) :
    proto.codec.CompData.write_payload proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self payload dst inf ⦃ r dst' inf' =>
      match self with
      | .Uncompressed _ => r = .Ok () ∧ dst'.val = dst.val ++ payload.val ∧ inf' = inf
      | .Compressed _ p =>
        inf' = some (Trusted.inflateState (inf.getD Trusted.decompressNew) payload p) ∧
        match Trusted.inflateResult (inf.getD Trusted.decompressNew) payload p with
        | .Ok v => r = .Ok () ∧ dst'.val = dst.val ++ v.val
        | .Err e => r = .Err e ∧ dst' = dst ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompData.write_payload_spec`
/-! ### `enum CompDecoder and its impls` -/

/-- `decode(src, dst, max_allowed_packet)`: total. It is exactly one step of `compStep`, inflating with a new stream, and gives the new state, input and output. The step's outcome is one of: more input needed, a compressed packet read, `PacketTooLarge`, `BadCompressedPacketHeader`, or an `Io` error from inflating. The only hypothesis is that the lengths computed fit in a `usize` (`compStepFits`). From a valid state, the new state is again valid. -/
recall proto.codec.CompDecoder.decode_spec (self : proto.codec.CompDecoder) (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : compStepFits (CompState.of self) dst.val) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r cd src' dst' =>
      (r, CompState.of cd, src'.val, dst'.val) =
        compStep (inflateList Trusted.decompressNew) (CompState.of self) src.val dst.val max.val ∧
      ((CompState.of self).Valid → (CompState.of cd).Valid) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompDecoder.decode_spec`
/-- Round trip for one packet. An idle decoder reads a compressed packet in the form the crate writes it (`compPacket`: stored, or a successful deflate of the piece) back to the piece. The result is `Ok(Last(seq))`, exactly the packet is consumed, and the decoder is idle again. (This rests on `Trusted.inflate_deflate`.) -/
recall proto.codec.CompDecoder.decode_compPacket (seq : U8) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = compPacket seq.val chunk zo ++ tail) (max : Usize)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val) (h : dst.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.CompDecoder.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut .Idle src dst max ⦃ r cd src' dst' =>
      r = .Ok (some (.Last seq)) ∧ cd = .Idle ∧ src'.val = tail ∧ dst'.val = dst.val ++ chunk ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompDecoder.decode_compPacket`
/-! ### `struct PacketCodec and its impls (with impl Default)` -/

/-- `reset_seq_id`: the sequence id becomes 0 (for a compressed codec, both the compressed and the plain one). -/
recall proto.codec.PacketCodec.reset_seq_id_eq (self : proto.codec.PacketCodec) :
    proto.codec.PacketCodec.reset_seq_id self = ok { self with inner := match self.inner with
      | .Plain c => .Plain { c with seq_id := 0#u8 }
      | .Comp c => .Comp { c with comp_seq_id := 0#u8, plain_codec := { c.plain_codec with seq_id := 0#u8 } } }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.reset_seq_id_eq`
/-- `sync_seq_id`: for a compressed codec with no decompressed input pending, the plain sequence id becomes the compressed one; otherwise nothing changes. -/
recall proto.codec.PacketCodec.sync_seq_id_eq (self : proto.codec.PacketCodec) :
    proto.codec.PacketCodec.sync_seq_id self = ok { self with inner := match self.inner with
      | .Plain c => .Plain c
      | .Comp c => .Comp (if c.in_buf.val = [] then
          { c with plain_codec := { c.plain_codec with seq_id := c.comp_seq_id } } else c) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.sync_seq_id_eq`
/-- `compress(level)`: `max_allowed_packet` is kept. On a plain codec, compression is turned on with compressed sequence id 0, empty buffers, an idle compressed-packet reader and no flate2 streams, and the plain codec (sequence id, chunk reader) is kept. On a compressed codec, a different level replaces the level and drops the deflate stream. Never panics, even for a level above 10 (see `compress_then_encode_panics`). -/
recall proto.codec.PacketCodec.compress_spec (self : proto.codec.PacketCodec) (lvl : flate2.Compression) :
    proto.codec.PacketCodec.compress self lvl ⦃ r =>
      r.max_allowed_packet = self.max_allowed_packet ∧
      match self.inner with
      | .Plain c => ∃ cc, r.inner = .Comp cc ∧ cc.level = lvl ∧ cc.comp_seq_id = 0#u8 ∧ cc.in_buf.val = [] ∧
          cc.out_buf.val = [] ∧ cc.comp_decoder = .Idle ∧ cc.deflater = none ∧ cc.inflater = none ∧
          cc.plain_codec = c
      | .Comp c => r.inner = if c.level.level = lvl.level then .Comp c else .Comp { c with level := lvl, deflater := none } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.compress_spec`
/-- `decode(src, dst)` on a plain codec: total; exactly `plainDecode` with the codec's `max_allowed_packet` and no compressed sequence id (as `PlainPacketCodec.decode_spec`). -/
recall proto.codec.PacketCodec.decode_plain_spec (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c)
    (hv : ∀ seq needed, c.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max)
    (src dst : proto.codec.buf_model.VecBuf) (h : dst.val.length + src.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst ⦃ r codec src' dst' =>
      codec.max_allowed_packet = self.max_allowed_packet ∧
      ∃ c', codec.inner = .Plain c' ∧
        (r, c'.seq_id, ChunkState.of c'.chunk_decoder, src'.val, dst'.val) =
          plainDecode c.seq_id (ChunkState.of c.chunk_decoder) src.val dst.val self.max_allowed_packet.val none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.decode_plain_spec`
/-- `decode(src, dst)` on a compressed codec: the compressed codec's `decode` with the codec's `max_allowed_packet` (see the `CompPacketCodec.decode_*` statements). -/
recall proto.codec.PacketCodec.decode_comp_eq (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (src dst : proto.codec.buf_model.VecBuf) :
    proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst =
      (do
        let (r, c', src', dst') ← proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst self.max_allowed_packet
        ok (r, { self with inner := .Comp c' }, src', dst'))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.decode_comp_eq`
/-- `encode(src, dst)` on a plain codec: `PacketTooLarge` (nothing changed) if the packet is longer than `max_allowed_packet`; otherwise its chunks (`frame`) are appended to `dst`, the packet is consumed, and the sequence id advances by the number of chunks (as `PlainPacketCodec.encode_spec`). -/
recall proto.codec.PacketCodec.encode_plain_spec (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c) (packet dst : proto.codec.buf_model.VecBuf)
    (h : self.max_allowed_packet.val < packet.val.length ∨ dst.val.length + (frame c.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst ⦃ r codec packet' dst' =>
      if self.max_allowed_packet.val < packet.val.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with inner := .Plain { c with seq_id := byte (c.seq_id.val + frameCount packet.val.length) } } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame c.seq_id.val packet.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.encode_plain_spec`
/-- `encode(src, dst)` on a compressed codec: the compressed codec's `encode` with the codec's `max_allowed_packet` (see `CompPacketCodec.encode_spec` and its panics). -/
recall proto.codec.PacketCodec.encode_comp_eq (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (packet dst : proto.codec.buf_model.VecBuf) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst =
      (do
        let (r, c', packet', dst') ← proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst self.max_allowed_packet
        ok (r, { self with inner := .Comp c' }, packet', dst'))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.encode_comp_eq`
/-- Headline round trip, plain codecs. Suppose a plain codec encodes a packet successfully. A plain codec with the same sequence id, an idle chunk reader and at least the same `max_allowed_packet` then decodes the bytes written (followed by anything) back to exactly the packet. The result is `Ok(true)`, with the input after them left, both sequence ids equal, and the reader idle. -/
recall proto.codec.PacketCodec.encode_decode_plain (enc dec : proto.codec.PacketCodec) (ce cd : proto.codec.PlainPacketCodec)
    (he : enc.inner = .Plain ce) (hd : dec.inner = .Plain cd) (hseq : cd.seq_id = ce.seq_id) (hidle : cd.chunk_decoder = .Idle)
    (hmax : enc.max_allowed_packet.val ≤ dec.max_allowed_packet.val)
    (packet dst : proto.codec.buf_model.VecBuf) (h : dst.val.length + (frame ce.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve enc packet dst ⦃ r enc' _ dst' =>
      r = .Ok () → ∃ ce', enc'.inner = .Plain ce' ∧
        ∀ (tail : List U8) (src d0 : proto.codec.buf_model.VecBuf), src.val = dst'.val.drop dst.val.length ++ tail → d0.val = [] →
          src.val.length + 2 ^ 24 ≤ Usize.max →
          proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut dec src d0 ⦃ r2 dec' src' d' =>
            r2 = .Ok true ∧ d'.val = packet.val ∧ src'.val = tail ∧
            ∃ cd', dec'.inner = .Plain cd' ∧ cd'.seq_id = ce'.seq_id ∧ cd'.chunk_decoder = .Idle ⦄ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.encode_decode_plain`
/-- Headline round trip, compressed codecs. Suppose a compressed codec with an empty output buffer encodes a packet successfully, without panicking (`max_allowed_packet ≠ 0`; level at most 10 or a kept deflate stream). The bytes it wrote (followed by anything) go to a compressed codec that has nothing pending, starts at the same two sequence ids, and has at least the same `max_allowed_packet`. That codec decodes them back to exactly the packet: `Ok(true)`, with the input after them left. Its compressed sequence id then equals the encoder's, its plain sequence id is advanced by the number of chunks, and nothing is pending. (The encoder instead sets its plain sequence id to the compressed one, as the server does.) Deflated pieces are read back by `Trusted.inflate_deflate`. -/
recall proto.codec.PacketCodec.encode_decode_comp (enc dec : proto.codec.PacketCodec) (ce cd : proto.codec.CompPacketCodec)
    (he : enc.inner = .Comp ce) (hd : dec.inner = .Comp cd) (hout : ce.out_buf.val = [])
    (hfresh : cd.in_buf.val = [] ∧ cd.comp_decoder = .Idle ∧ cd.plain_codec.chunk_decoder = .Idle)
    (hseq : cd.comp_seq_id = ce.comp_seq_id ∧ cd.plain_codec.seq_id = ce.plain_codec.seq_id)
    (hmax0 : enc.max_allowed_packet.val ≠ 0) (hmax : enc.max_allowed_packet.val ≤ dec.max_allowed_packet.val)
    (hlvl : ce.deflater ≠ none ∨ ce.level.level.val ≤ 10)
    (packet dst : proto.codec.buf_model.VecBuf) (h : dst.val.length + 8 * (frame ce.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve enc packet dst ⦃ r enc' _ dst' =>
      r = .Ok () → ∃ ce', enc'.inner = .Comp ce' ∧
        ∀ (tail : List U8) (src d0 : proto.codec.buf_model.VecBuf), src.val = dst'.val.drop dst.val.length ++ tail → d0.val = [] →
          2 ^ 25 * (src.val.length + 1) ≤ Usize.max →
          proto.codec.PacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut dec src d0 ⦃ r2 dec' src' d' =>
            r2 = .Ok true ∧ d'.val = packet.val ∧ src'.val = tail ∧
            ∃ cd', dec'.inner = .Comp cd' ∧ cd'.comp_seq_id = ce'.comp_seq_id ∧
              cd'.plain_codec.seq_id = byte (ce.plain_codec.seq_id.val + frameCount packet.val.length) ∧
              cd'.in_buf.val = [] ∧ cd'.comp_decoder = .Idle ∧ cd'.plain_codec.chunk_decoder = .Idle ⦄ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.encode_decode_comp`
/-- **Upstream bug:** a compressed codec with `max_allowed_packet = 0` panics when encoding an empty packet (`chunks(0)` in `compress_with`), instead of returning an error. -/
recall proto.codec.PacketCodec.encode_comp_max_zero (self : proto.codec.PacketCodec) (c : proto.codec.CompPacketCodec)
    (hc : self.inner = .Comp c) (hmax : self.max_allowed_packet.val = 0) (packet dst : proto.codec.buf_model.VecBuf)
    (hp : packet.val = []) (h : c.out_buf.val.length + 4 ≤ Usize.max) :
    proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.encode_comp_max_zero`
/-- A compression level above 10 is accepted by `compress`, but the first `encode` that deflates then panics: one whose packet (within `max_allowed_packet`) has chunks making a first piece of at least `minCompressLength` bytes. This is flate2's miniz_oxide `debug_assert!(level <= 10)` in `Compress::new`; the default zlib backend, outside the verified configuration, instead panics above 9 in every profile. -/
recall proto.codec.PacketCodec.compress_then_encode_panics (self : proto.codec.PacketCodec) (c : proto.codec.PlainPacketCodec)
    (hc : self.inner = .Plain c) (lvl : flate2.Compression) (hlvl : 10 < lvl.level.val)
    (packet dst : proto.codec.buf_model.VecBuf) (hp : packet.val.length ≤ self.max_allowed_packet.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize self.max_allowed_packet.val) (frame c.seq_id.val packet.val).length)
    (h : dst.val.length + 8 * (frame c.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PacketCodec.compress self lvl ⦃ c2 =>
      proto.codec.PacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c2 packet dst = fail .panic ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.compress_then_encode_panics`
/-- `Default`: a plain codec with sequence id 0, an idle chunk reader and `max_allowed_packet` = `DEFAULT_MAX_ALLOWED_PACKET` = 4 MiB. -/
recall proto.codec.PacketCodec.default_eq :
    proto.codec.PacketCodec.Insts.CoreDefaultDefault.default =
      ok { max_allowed_packet := 4194304#usize, inner := .Plain { seq_id := 0#u8, chunk_decoder := .Idle } }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodec.default_eq`
/-! ### `enum PacketCodecInner and its impls (with impl Default)` -/

/-- `reset_seq_id`: the sequence id of the plain codec, or both sequence ids of the compressed codec, become 0. -/
recall proto.codec.PacketCodecInner.reset_seq_id_eq (self : proto.codec.PacketCodecInner) :
    proto.codec.PacketCodecInner.reset_seq_id self = ok (match self with
      | .Plain c => .Plain { c with seq_id := 0#u8 }
      | .Comp c => .Comp { c with comp_seq_id := 0#u8, plain_codec := { c.plain_codec with seq_id := 0#u8 } })

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.reset_seq_id_eq`
/-- `sync_seq_id`: nothing for the plain codec. For the compressed codec, the plain sequence id becomes the compressed one if no decompressed input is pending. -/
recall proto.codec.PacketCodecInner.sync_seq_id_eq (self : proto.codec.PacketCodecInner) :
    proto.codec.PacketCodecInner.sync_seq_id self = ok (match self with
      | .Plain c => .Plain c
      | .Comp c => .Comp (if c.in_buf.val = [] then
          { c with plain_codec := { c.plain_codec with seq_id := c.comp_seq_id } } else c))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.sync_seq_id_eq`
/-- `compress(level)`. On a plain codec, compression is turned on: the compressed sequence id is 0, the buffers are empty, the compressed-packet reader is idle, there are no flate2 streams yet, and the plain codec (sequence id and chunk reader) is kept as it was. On a compressed codec, a different level replaces the level and drops the deflate stream, and the same level changes nothing. Never panics, even for a level above 10 (that panic comes at the first deflate, see `CompPacketCodec.encode_level_panic`). -/
recall proto.codec.PacketCodecInner.compress_spec (self : proto.codec.PacketCodecInner) (lvl : flate2.Compression) :
    proto.codec.PacketCodecInner.compress self lvl ⦃ r =>
      match self with
      | .Plain c => ∃ cc, r = .Comp cc ∧ cc.level = lvl ∧ cc.comp_seq_id = 0#u8 ∧ cc.in_buf.val = [] ∧
          cc.out_buf.val = [] ∧ cc.comp_decoder = .Idle ∧ cc.deflater = none ∧ cc.inflater = none ∧
          cc.plain_codec = c
      | .Comp c => r = if c.level.level = lvl.level then .Comp c else .Comp { c with level := lvl, deflater := none } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.compress_spec`
/-- `decode(src, dst, max_allowed_packet)`: the plain codec's `decode` without a compressed sequence id, or the compressed codec's `decode`. -/
recall proto.codec.PacketCodecInner.decode_eq (self : proto.codec.PacketCodecInner) (src dst : proto.codec.buf_model.VecBuf) (max : Usize) :
    proto.codec.PacketCodecInner.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max =
      (match self with
      | .Plain c => do
        let (r, c', src', dst') ← proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst max none
        ok (r, .Plain c', src', dst')
      | .Comp c => do
        let (r, c', src', dst') ← proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst max
        ok (r, .Comp c', src', dst'))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.decode_eq`
/-- `encode(packet, dst, max_allowed_packet)`: the plain or the compressed codec's `encode`. -/
recall proto.codec.PacketCodecInner.encode_eq (self : proto.codec.PacketCodecInner) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize) :
    proto.codec.PacketCodecInner.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max =
      (match self with
      | .Plain c => do
        let (r, c', packet', dst') ← proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst max
        ok (r, .Plain c', packet', dst')
      | .Comp c => do
        let (r, c', packet', dst') ← proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve c packet dst max
        ok (r, .Comp c', packet', dst'))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.encode_eq`
/-- `Default`: a plain codec with sequence id 0 and an idle chunk reader. -/
recall proto.codec.PacketCodecInner.default_eq :
    proto.codec.PacketCodecInner.Insts.CoreDefaultDefault.default =
      ok (.Plain { seq_id := 0#u8, chunk_decoder := .Idle })

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PacketCodecInner.default_eq`
/-! ### `struct PlainPacketCodec and its impls` -/

/-- `reset_seq_id`: the sequence id becomes 0. -/
recall proto.codec.PlainPacketCodec.reset_seq_id_eq (self : proto.codec.PlainPacketCodec) :
    proto.codec.PlainPacketCodec.reset_seq_id self = ok { self with seq_id := 0#u8 }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.reset_seq_id_eq
/-- `encode(packet, dst, max_allowed_packet)`: `PacketTooLarge`, nothing changed, if the packet is longer than `max_allowed_packet`; otherwise appends its chunks from the codec's sequence id (`frame`), consumes the packet, and advances the sequence id by the number of chunks. -/
recall proto.codec.PlainPacketCodec.encode_spec (self : proto.codec.PlainPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : max.val < packet.length ∨ dst.length + (frame self.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.PlainPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r codec packet' dst' =>
      if max.val < packet.length then
        r = .Err .PacketTooLarge ∧ codec = self ∧ packet' = packet ∧ dst' = dst
      else
        r = .Ok () ∧ codec = { self with seq_id := byte (self.seq_id.val + frameCount packet.length) } ∧
        packet'.val = [] ∧ dst'.val = dst.val ++ frame self.seq_id.val packet.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.encode_spec
/-- `decode(src, dst, max_allowed_packet, comp_seq_id)`: total; exactly `plainDecode` (chunks read with `chunkStep` until the last chunk of a packet, `Ok(true)`, or more input is needed, `Ok(false)`, or an error: `PacketTooLarge`, or `PacketsOutOfSync` for a chunk whose sequence id is neither the expected one nor `comp_seq_id`). The decoder state need not be one the decoder produces: a pending length only has to satisfy `4 + needed ≤ usize::MAX` (`hv`). From a valid state the new state is again valid. -/
recall proto.codec.PlainPacketCodec.decode_spec (self : proto.codec.PlainPacketCodec)
    (hv : ∀ seq needed, self.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (comp : Option U8)
    (h : dst.length + src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id (ChunkState.of self.chunk_decoder) src.val dst.val max.val comp ∧
      ((ChunkState.of self.chunk_decoder).Valid → (ChunkState.of codec.chunk_decoder).Valid) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_spec
/-- Headline round trip: an idle codec decodes the chunks of a payload (`frame`, as `encode` writes them) starting at its sequence id into an empty `dst`: the whole payload, `Ok(true)`, the input after the chunks left, the sequence id advanced by the number of chunks, the decoder idle again. -/
recall proto.codec.PlainPacketCodec.decode_frame (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame self.seq_id.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
      codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_frame
/-- Incremental decoding: on a strict prefix of the chunks of a payload, an idle codec reports that more input is needed (`Ok(false)`), never an error; the state it leaves is `plainDecode`'s (see `decode_resume` for continuing). -/
recall proto.codec.PlainPacketCodec.decode_prefix (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r codec src' dst' =>
      r = .Ok false ∧
      (r, codec.seq_id, ChunkState.of codec.chunk_decoder, src'.val, dst'.val) =
        plainDecode self.seq_id ChunkState.idle ((frame self.seq_id.val p).take k) [] max.val comp ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_prefix
/-- Resumption: after decoding a strict prefix of the chunks of a payload (`Ok(false)`), calling `decode` again with the returned codec and output, on what the first call left of the input followed by the rest of the chunks (and anything after), completes the packet: `Ok(true)`, the whole payload, the sequence id advanced by the number of chunks, the decoder idle, the input after the chunks left. -/
recall proto.codec.PlainPacketCodec.decode_resume (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (p tail : List U8) (k : Nat)
    (hk : k < (frame self.seq_id.val p).length) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val = (frame self.seq_id.val p).take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val) (comp : Option U8)
    (h : (frame self.seq_id.val p).length + tail.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max comp ⦃ r1 codec1 src1 dst1 =>
      r1 = .Ok false ∧
      ∀ src2 : proto.codec.buf_model.VecBuf, src2.val = src1.val ++ (frame self.seq_id.val p).drop k ++ tail →
        (proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut codec1 src2 dst1 max comp ⦃ r codec src' dst' =>
          r = .Ok true ∧ codec.seq_id = byte (self.seq_id.val + frameCount p.length) ∧
          codec.chunk_decoder = .Idle ∧ src'.val = tail ∧ dst'.val = p ⦄) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_resume
/-- Out of sync: an idle codec given (outside compressed mode) the chunks of a payload whose sequence id `s` is not the expected one fails with `PacketsOutOfSync`; its expected sequence id is unchanged and its chunk decoder is idle again (the first chunk has been consumed). Only the first chunk has to pass the size check (`hmax`). -/
recall proto.codec.PlainPacketCodec.decode_out_of_sync (self : proto.codec.PlainPacketCodec) (hidle : self.chunk_decoder = .Idle) (s : U8) (hs : s ≠ self.seq_id)
    (p tail : List U8) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = frame s.val p ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : min p.length maxPayloadLen ≤ max.val) (h : src.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.PlainPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max none ⦃ r codec _ _ =>
      r = .Err .PacketsOutOfSync ∧ codec.seq_id = self.seq_id ∧ codec.chunk_decoder = .Idle ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.PlainPacketCodec.decode_out_of_sync
/-! ### `struct CompPacketCodec and its impls` -/

/-- `reset_seq_id`: both the compressed and the plain sequence ids become 0. -/
recall proto.codec.CompPacketCodec.reset_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.reset_seq_id self =
      ok { self with comp_seq_id := 0#u8, plain_codec := { self.plain_codec with seq_id := 0#u8 } }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.reset_seq_id_eq`
/-- `sync_seq_id`: if no decompressed input is pending (`in_buf` empty, i.e. on a compressed-packet boundary), the plain sequence id becomes the compressed one; otherwise nothing changes. -/
recall proto.codec.CompPacketCodec.sync_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.sync_seq_id self =
      ok (if self.in_buf.val = [] then
            { self with plain_codec := { self.plain_codec with seq_id := self.comp_seq_id } }
          else self)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.sync_seq_id_eq`
/-- `decode(src, dst, max_allowed_packet)`: total. It never panics, and states the decoder can produce stay valid. It decodes compressed packets from `src` into the internal buffer `in_buf`, and plain packets from `in_buf` into `dst` (see the round-trip, streaming and error statements below).
    The hypotheses: the pending states are valid (`CompState.Valid`, `ChunkState.Valid`; the decoder only produces valid states, but the enum fields are public), and a size bound that rules out `usize` overflow. That bound is stronger than necessary: each compressed packet of at least 7 input bytes can add up to `2^24` bytes to `in_buf`. -/
recall proto.codec.CompPacketCodec.decode_total (self : proto.codec.CompPacketCodec)
    (hc : (CompState.of self.comp_decoder).Valid) (hp : (ChunkState.of self.plain_codec.chunk_decoder).Valid)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : 2 ^ 25 * (self.in_buf.val.length + src.val.length + dst.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ _ c' _ _ =>
      (CompState.of c'.comp_decoder).Valid ∧ (ChunkState.of c'.plain_codec.chunk_decoder).Valid ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_total`
/-- Headline round trip (decoding). Take a decoder with nothing pending (`in_buf` empty, both readers idle). Feed it a compressed stream of the chunks of a payload `p` (`CompEncoding` of `frame`, as `encode` writes them, cut into pieces of any size `n` up to `min(2^24 - 1, max_allowed_packet)`), followed by anything. It gives back exactly `p`, with `Ok(true)` and the input after the stream left. The compressed sequence id is advanced by the number of compressed packets and the plain one by the number of chunks, and nothing is pending again. The stream must start at the decoder's two sequence ids. Deflated pieces are read back by `Trusted.inflate_deflate`, with whatever inflate stream the decoder holds. -/
recall proto.codec.CompPacketCodec.decode_compEncoding (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (lvl n : Nat) (hn : 0 < n ∧ n ≤ maxPayloadLen) (p out tail : List U8)
    (henc : CompEncoding lvl n self.comp_seq_id.val (frame self.plain_codec.seq_id.val p) out)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out ++ tail) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val ∧ n ≤ max.val)
    (h : 2 ^ 25 * (src.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧
      c'.comp_seq_id = byte (self.comp_seq_id.val + (chunksOf n (frame self.plain_codec.seq_id.val p)).length) ∧
      c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
      c'.in_buf.val = [] ∧ c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_compEncoding`
/-- Streaming. On a strict prefix of such a compressed stream, a decoder with nothing pending reports that more input is needed (`Ok(false)`), never an error. (Plain chunks completed so far may already be in `dst`.) -/
recall proto.codec.CompPacketCodec.decode_prefix (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (lvl n : Nat) (hn : 0 < n ∧ n ≤ maxPayloadLen) (p out : List U8)
    (henc : CompEncoding lvl n self.comp_seq_id.val (frame self.plain_codec.seq_id.val p) out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val ∧ n ≤ max.val)
    (h : 2 ^ 25 * (out.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r _ _ _ =>
      r = .Ok false ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_prefix`
/-- Resumption. Decode a strict prefix of such a compressed stream (`Ok(false)`). Then call `decode` again with the returned codec and output, on what the first call left of the input followed by the rest of the stream (and anything after). This completes the packet: `Ok(true)`, exactly `p`, the input after the stream left, both sequence ids advanced as in `decode_compEncoding`, and nothing pending. -/
recall proto.codec.CompPacketCodec.decode_resume (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (lvl n : Nat) (hn : 0 < n ∧ n ≤ maxPayloadLen) (p out tail : List U8)
    (henc : CompEncoding lvl n self.comp_seq_id.val (frame self.plain_codec.seq_id.val p) out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (max : Usize) (hmax : p.length ≤ max.val ∧ n ≤ max.val)
    (h : 2 ^ 25 * (out.length + tail.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r1 c1 src1 dst1 =>
      r1 = .Ok false ∧
      ∀ src2 : proto.codec.buf_model.VecBuf, src2.val = src1.val ++ out.drop k ++ tail →
        (proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c1 src2 dst1 max ⦃ r c' src' dst' =>
          r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧
          c'.comp_seq_id = byte (self.comp_seq_id.val + (chunksOf n (frame self.plain_codec.seq_id.val p)).length) ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
          c'.in_buf.val = [] ∧ c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_resume`
/-- Out of sync. A decoder with nothing pending, given a compressed packet (as the crate writes them) whose sequence id `s` is not the expected one, fails with `PacketsOutOfSync`; the compressed sequence id is unchanged. **Quirk:** the packet has been consumed, and its plain bytes have been kept in `in_buf`, so a later call would decode them. -/
recall proto.codec.CompPacketCodec.decode_out_of_sync (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (s : U8) (hs : s ≠ self.comp_seq_id) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = compPacket s.val chunk zo ++ tail)
    (max : Usize) (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val)
    (h : dst.val.length + 2 ^ 25 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketsOutOfSync ∧ c'.comp_seq_id = self.comp_seq_id ∧ c'.comp_decoder = .Idle ∧
      c'.in_buf.val = chunk ∧ src'.val = tail ∧ dst' = dst ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_out_of_sync`
/-- A compressed-packet header with a length above `max_allowed_packet` (either length), seen with nothing pending: `PacketTooLarge`, and nothing changes (the codec, input and output are as before). -/
recall proto.codec.CompPacketCodec.decode_too_large (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hbig : max.val < Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketTooLarge ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_too_large`
/-- A compressed-packet header with compressed length 0 but a non-zero uncompressed length, within `max_allowed_packet`, seen with nothing pending: `BadCompressedPacketHeader`, and nothing changes. -/
recall proto.codec.CompPacketCodec.decode_bad_header (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hcl : (compHeaderRead src.val).1 = 0) (hpl : (compHeaderRead src.val).2.2 ≠ 0)
    (hmax : (compHeaderRead src.val).2.2 ≤ max.val) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .BadCompressedPacketHeader ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_bad_header`
/-- Inflate failure. A whole compressed packet (non-zero lengths within `max_allowed_packet`) whose payload the decoder's inflate stream fails to inflate to the declared length, seen with nothing pending, gives `Err(Io(e))` with flate2's error. **Quirk:** the 7 header bytes have been consumed, but the packet reader stays in the pending state of that header. A later call would therefore read the payload's bytes as if a header still preceded them, unless the codec is discarded (as callers do after an error). -/
recall proto.codec.CompPacketCodec.decode_inflate_error (self : proto.codec.CompPacketCodec)
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
        .packet (compHeaderRead src.val).2.1 (compHeaderRead src.val).1 (compHeaderRead src.val).2.2 ∧
      src'.val = src.val.drop 7 ∧ dst' = dst ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.decode_inflate_error`
/-- `encode(packet, dst, max_allowed_packet)`, whenever it does not panic (`max_allowed_packet ≠ 0` or the packet is too large; level at most 10, a kept deflate stream, or no piece long enough to deflate).
    * `PacketTooLarge` if the packet is longer than `max_allowed_packet`; nothing changes.
    * Otherwise the packet's chunks (`frame`, from the plain sequence id) are appended to `out_buf`, and `out_buf` is compressed into `dst` (`CompEncoding`, from the compressed sequence id; see `compress_with_spec`). The packet is consumed.
      - On `Ok`: `out_buf` is emptied, the compressed sequence id is advanced by the number of compressed packets, and the plain sequence id is set to it (synchronised as in the server's `net_serv.cc`).
      - On `Err`: deflating failed (an `Io` error). **Quirk:** the plain sequence id has already advanced, but the compressed one has not, and the chunks stay in `out_buf`, so the next `encode` sends them again ahead of its own packet. `dst` holds the compressed packets of the pieces before the failure.
    The reading side (`in_buf`, the readers, the inflate stream) and the level are untouched. The deflate stream is not described. -/
recall proto.codec.CompPacketCodec.encode_spec (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
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
          ∃ out, CompEncoding self.level.level.val (compChunkSize max.val) self.comp_seq_id.val
              (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val) out ∧
            dst'.val = dst.val ++ out
        | .Err e =>
          (∃ ioe, e = .Io ioe) ∧ c'.comp_seq_id = self.comp_seq_id ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount packet.val.length) ∧
          c'.out_buf.val = self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val ∧
          ∃ k out, k < (chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).length ∧
            self.level.level.val ≠ 0 ∧
            CompPacketsOf self.level.level.val self.comp_seq_id.val
              ((chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).take k) out ∧
            dst'.val = dst.val ++ out ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.encode_spec`
/-- **Upstream bug:** with `max_allowed_packet = 0`, encoding an empty packet panics. The empty packet passes the size check, its one empty chunk (4 bytes) goes to `out_buf`, and compressing it calls `chunks(0)`. (A non-empty packet gets `PacketTooLarge` instead.) -/
recall proto.codec.CompPacketCodec.encode_max_zero (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf)
    (hp : packet.val = []) (h : self.out_buf.val.length + 4 ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst 0#usize = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.encode_max_zero`
/-- With no deflate stream yet and a level above 10, `encode` of a packet within `max_allowed_packet` panics when the first piece of `out_buf` (after the packet's chunks are added) has at least `minCompressLength` bytes. This is flate2's `debug_assert!` in `Compress::new`. -/
recall proto.codec.CompPacketCodec.encode_level_panic (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (hd : self.deflater = none) (hlvl : 10 < self.level.level.val) (hp : packet.val.length ≤ max.val)
    (hbig : minCompressLength ≤
      Nat.min (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length)
    (h : self.out_buf.val.length + (frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max ∧
      dst.val.length + 8 * (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.CompPacketCodec.encode_level_panic`
end mysql_common
