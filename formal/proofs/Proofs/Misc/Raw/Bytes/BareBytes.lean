import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impl BytesRepr for BareBytes<MAX_LEN>` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `BareBytes<MAX_LEN>::MAX_LEN`: `MAX_LEN`. -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN M = M := by
  unfold misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN; rfl

/-- `BareBytes<MAX_LEN>::SIZE` is `None`. -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE M = none := by
  unfold misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE; rfl

/-- `BareBytes<MAX_LEN>::serialize`: appends the bytes, truncated to `MAX_LEN` (no length is written: it is stored elsewhere). -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec (M : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + min text.length M.val ≤ Usize.max) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize M text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take M.val ⦄ := by
  unfold misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize
  step as ⟨ len, hlen ⟩
  step as ⟨ s, hs1, hs2 ⟩
  step as ⟨ v, hv ⟩
  simp [hv, hs1, hlen, List.slice, Nat.min_comm]

/-- `BareBytes<MAX_LEN>::deserialize`: total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. (`MAX_LEN` is not checked.) -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec (M : Usize) (len : Usize) (buf : io.ParseBuf) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize M len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map cowList = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize
  step with io.ParseBuf.checked_eat_spec as ⟨ o, rest, ho ⟩
  split at ho
  · obtain ⟨ho1, ho2⟩ := ho
    cases o <;> simp_all [okPart, cowList]
  · obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp_all [okPart, misc.unexpected_buf_eof, misc.io_error_msg]

end mysql_common
