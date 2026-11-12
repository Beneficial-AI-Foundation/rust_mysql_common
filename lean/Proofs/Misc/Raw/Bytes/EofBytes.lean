import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impl BytesRepr for EofBytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `EofBytes::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max := by
  unfold misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.Usize.MAX]

/-- `EofBytes::SIZE` is `None`. -/
theorem misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `EofBytes::serialize`: appends the bytes. -/
theorem misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + text.length ≤ Usize.max) :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ text.val ⦄ := by
  unfold misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  step as ⟨ v, hv ⟩
  simp [hv]

/-- `EofBytes::deserialize`: total; the rest of the buffer. -/
theorem misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map cowList = some buf.val ∧ rest.val = [] ⦄ := by
  unfold misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with io.ParseBuf.eat_all_spec as ⟨ s, rest, hs, hr ⟩
  simp_all [okPart, cowList]

end mysql_common
