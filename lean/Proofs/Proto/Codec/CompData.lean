import Defs

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
  sorry

/-- `needed`: the compressed length of either variant. -/
theorem proto.codec.CompData.needed_eq (d : proto.codec.CompData) :
    proto.codec.CompData.needed d = ok (match d with | .Compressed n _ => n | .Uncompressed n => n) := by
  sorry

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
  sorry

end mysql_common
