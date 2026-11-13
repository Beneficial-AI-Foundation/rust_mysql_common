import Defs

/-! Statements for `fn compress_with` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `compress_with(.., deflater, ..)` on an empty `src`: `Ok(0)`, nothing changed (the same quirk as `compress`). -/
theorem proto.codec.compress_with_empty (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d max src dst = ok (.Ok 0#u8, d, src, dst) := by
  sorry

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). `compress_with` with `max_allowed_packet = 0` on a non-empty `src` panics (`chunks(0)`). -/
theorem proto.codec.compress_with_max_zero (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val ≠ []) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl d 0#usize src dst = fail .panic := by
  sorry

/-- `compress_with` with no deflate stream yet and a level above 10 panics when it creates one, i.e. when the first piece has at least `minCompressLength` bytes (flate2's `debug_assert!(level <= 10)`, `src/ffi/miniz_oxide.rs:153`: debug builds only, no panic in release). -/
theorem proto.codec.compress_with_level_panic (seq : U8) (lvl : flate2.Compression) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
    (hsrc : src.val ≠ []) (hmax : max.val ≠ 0) (hlvl : 10 < lvl.level.val)
    (hbig : minCompressLength ≤ Nat.min (compChunkSize max.val) src.val.length) :
    proto.codec.compress_with proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve seq lvl none max src dst = fail .panic := by
  sorry

/-- `compress_with(seq_id, compression, deflater, max_allowed_packet, src, dst)` on a non-empty `src`, whenever it does not panic: as `compress_spec`. A kept deflate stream is reused and never re-created, so the level is then not checked. The new stream is not described (it is opaque flate2 state). -/
theorem proto.codec.compress_with_spec (seq : U8) (lvl : flate2.Compression) (d : Option flate2.mem.Compress) (max : Usize) (src dst : proto.codec.buf_model.VecBuf)
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
          dst'.val = dst.val ++ out ⦄ := by
  sorry

end mysql_common
