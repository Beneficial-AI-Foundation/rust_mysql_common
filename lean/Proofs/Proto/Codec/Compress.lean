import Defs

/-! Statements for `fn compress` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `compress(seq_id, compression, max_allowed_packet, src, dst)` on an empty `src`: `Ok(0)`, nothing changed. **Quirk:** the result is `0`, not the given `seq_id` (upstream returns early with `Ok(0)`). The crate's own codec never calls it with an empty buffer. -/
theorem proto.codec.compress_empty (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = []) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst = ok (.Ok 0#u8, src, dst) := by
  sorry

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). `compress` with `max_allowed_packet = 0` on a non-empty `src` panics (`src.chunks(0)`; the patched copy has the same `assert!`) instead of returning an error. -/
theorem proto.codec.compress_max_zero (seq : U8) (lvl : flate2.Compression) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val ≠ []) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl 0#usize src dst = fail .panic := by
  sorry

/-- `compress` at a compression level above 10 panics as soon as it deflates, i.e. when the first piece has at least `minCompressLength` bytes. This is flate2's `debug_assert!(level <= 10)` in `Compress::new` (`src/ffi/miniz_oxide.rs:153`): debug builds only (the proofs use debug semantics), no panic in release. -/
theorem proto.codec.compress_level_panic (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0) (hlvl : 10 < lvl.level.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize max.val) src.val.length) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst = fail .panic := by
  sorry

/-- `compress(seq_id, compression, max_allowed_packet, src, dst)` on a non-empty `src`, whenever it does not panic (`max_allowed_packet ≠ 0`, and a level of at most 10 or no piece long enough to deflate). `src` is cut into pieces of `min(2^24 - 1, max_allowed_packet)` bytes (`chunksOf`, `compChunkSize`). Each piece is sent as one compressed packet (`CompEncoding`), with sequence ids counting up from `seq_id`. A piece is deflated when the level is not 0, the piece has at least 512 bytes and deflating made it shorter, and stored otherwise (`EncChoice`).
    * `Ok(s)`: `s` is `seq_id` plus the number of packets (mod 256), `src` is emptied, and the packets are appended to `dst`.
    * `Err(e)`: only when deflating a piece failed. Then `e` is an `Io` error, the level is not 0, and that piece has at least 512 bytes. `src` is unchanged, and `dst` has the packets of the pieces before it.
    The size bound only rules out `usize` overflow. -/
theorem proto.codec.compress_spec (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0)
    (hlvl : lvl.level.val ≤ 10 ∨ Nat.min (compChunkSize max.val) src.val.length < minCompressLength)
    (h : dst.val.length + 8 * src.val.length ≤ Usize.max) :
    proto.codec.compress proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl max src dst ⦃ r src' dst' =>
      match r with
      | .Ok s =>
        s = byte (seq.val + (chunksOf (compChunkSize max.val) src.val).length) ∧ src'.val = [] ∧
        ∃ out, CompEncoding (Trusted.compressNew lvl) lvl.level.val (compChunkSize max.val) seq.val src.val out ∧ dst'.val = dst.val ++ out
      | .Err e =>
        (∃ ioe, e = .Io ioe) ∧ src' = src ∧
        ∃ k out, k < (chunksOf (compChunkSize max.val) src.val).length ∧ lvl.level.val ≠ 0 ∧
          minCompressLength ≤ ((chunksOf (compChunkSize max.val) src.val).getD k []).length ∧
          CompPacketsOf (Trusted.compressNew lvl) lvl.level.val seq.val ((chunksOf (compChunkSize max.val) src.val).take k) out ∧
          dst'.val = dst.val ++ out ⦄ := by
  sorry

end mysql_common
