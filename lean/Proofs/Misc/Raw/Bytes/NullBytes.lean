import Defs

/-! Statements for `impl BytesRepr for NullBytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `NullBytes::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max := by
  sorry

/-- `NullBytes::SIZE` is `None`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  sorry

/-- `NullBytes::serialize`: appends the bytes before the first `0` (all of them if there is none), then a `0`: a string containing `0` is silently truncated. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + text.length ≤ Usize.max) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ beforeZero text.val ++ [byte 0] ⦄ := by
  sorry

/-- `NullBytes::deserialize`: total; the bytes before the first `0`, consuming the `0`; an error (its kind is not stated: `io::Error` is opaque; documented as `InvalidData`) with the buffer unchanged if there is no `0`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      if ∃ b ∈ buf.val, b.val = 0 then
        (okPart r).map cowList = some (beforeZero buf.val) ∧
        rest.val = buf.val.drop ((beforeZero buf.val).length + 1)
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip, for strings without a `0` byte. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : ∀ b ∈ s, b.val ≠ 0) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = s ++ [byte 0] ++ tail) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
