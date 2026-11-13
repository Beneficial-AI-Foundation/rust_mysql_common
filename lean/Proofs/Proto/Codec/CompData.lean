import Defs
import Proofs.Util.CompCodec

/-! Statements for `enum CompData and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `CompData::new(compressed_len, uncompressed_len, max_allowed_packet)`:
    * `PacketTooLarge` if either length exceeds `max_allowed_packet` (this is checked first);
    * otherwise, with compressed length 0: `None` (an empty packet) if the uncompressed length is also 0, and `BadCompressedPacketHeader` if not;
    * otherwise `Uncompressed` (stored) if the uncompressed length is 0, and `Compressed` if not. -/
theorem proto.codec.CompData.new_eq (cl pl max : Usize) :
    proto.codec.CompData.new cl pl max = ok
      (if max.val < Nat.max cl.val pl.val then .Err .PacketTooLarge
       else if cl.val = 0 then (if pl.val = 0 then .Ok none else .Err .BadCompressedPacketHeader)
       else .Ok (some (if pl.val = 0 then .Uncompressed cl else .Compressed cl pl))) := by
  unfold proto.codec.CompData.new
  have hc : (cl != 0#usize) = !decide (cl.val = 0) := by
    by_cases h : cl.val = 0 <;> simp [h, UScalar.eq_equiv]
  have hp : (pl != 0#usize) = !decide (pl.val = 0) := by
    by_cases h : pl.val = 0 <;> simp [h, UScalar.eq_equiv]
  simp only [core.cmp.max, proto.codec.buf_model.NonZeroUsize.new, liftFun2, bind_ok, hc, hp, gt_iff_lt,
    UScalar.lt_equiv, core.cmp.impls.OrdUsize.max_val]
  by_cases h1 : max.val < Nat.max cl.val pl.val <;> by_cases h2 : cl.val = 0 <;>
    by_cases h3 : pl.val = 0 <;> simp [h1, h2, h3] <;> split_ifs <;> rfl

/-- `needed`: the compressed length of either variant. -/
theorem proto.codec.CompData.needed_eq (d : proto.codec.CompData) :
    proto.codec.CompData.needed d = ok (match d with | .Compressed n _ => n | .Uncompressed n => n) := by
  cases d <;> simp [proto.codec.CompData.needed, proto.codec.buf_model.NonZeroUsize.get]

/-- `write_payload(payload, dst, inflater)`. A stored payload is appended to `dst` as is. A compressed one is inflated to its uncompressed length with the kept stream (or a new one); on success the result is appended to `dst`, and on failure the error is returned and `dst` is unchanged. The stream is kept in both cases. -/
theorem proto.codec.CompData.write_payload_spec (self : proto.codec.CompData) (payload : Slice U8) (dst : proto.codec.buf_model.VecBuf)
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
        | .Err e => r = .Err e ∧ dst' = dst ⦄ := by
  cases self with
  | Uncompressed n =>
    simp only [proto.codec.CompData.write_payload]
    step*
  | Compressed n p =>
    have hlen := Trusted.inflateResult_len (inf.getD Trusted.decompressNew) payload p
    simp only at h
    cases inf with
    | none =>
      simp only [proto.codec.CompData.write_payload, proto.codec.trusted.decompress_new,
        proto.codec.buf_model.NonZeroUsize.get, proto.codec.trusted.inflate,
        core.result.Result.Insts.CoreOpsTry.branch]
      simp only [Option.getD_none] at hlen ⊢
      cases hr : Trusted.inflateResult Trusted.decompressNew payload p with
      | Ok v =>
        have := hlen v hr
        obtain ⟨d', hd', hp'⟩ := PBUtil.spec_eq_ok (CompCodec.vb_put_slice_spec dst (alloc.vec.Vec.deref v)
          (by simp [alloc.vec.Vec.deref]; omega))
        simp [hr, hd']
        simpa [alloc.vec.Vec.deref] using hp'
      | Err e =>
        simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
    | some i =>
      simp only [proto.codec.CompData.write_payload,
        proto.codec.buf_model.NonZeroUsize.get, proto.codec.trusted.inflate,
        core.result.Result.Insts.CoreOpsTry.branch]
      simp only [Option.getD_some] at hlen ⊢
      cases hr : Trusted.inflateResult i payload p with
      | Ok v =>
        have := hlen v hr
        obtain ⟨d', hd', hp'⟩ := PBUtil.spec_eq_ok (CompCodec.vb_put_slice_spec dst (alloc.vec.Vec.deref v)
          (by simp [alloc.vec.Vec.deref]; omega))
        simp [hr, hd']
        simpa [alloc.vec.Vec.deref] using hp'
      | Err e =>
        simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]

end mysql_common
