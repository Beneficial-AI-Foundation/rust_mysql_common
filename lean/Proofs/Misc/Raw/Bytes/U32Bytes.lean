import Defs

/-! Statements for `impl BytesRepr for U32Bytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `U32Bytes::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  sorry

/-- `U32Bytes::SIZE` is `None`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  sorry

/-- `U32Bytes::serialize`: appends a little-endian `u32` length and the bytes, truncated to `u32::MAX` bytes (documented). -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + min text.length (2 ^ 32 - 1) ≤ Usize.max) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min text.length (2 ^ 32 - 1)) ++ text.val.take (2 ^ 32 - 1) ⦄ := by
  sorry

/-- `U32Bytes::deserialize`: total; `checkedLenPrefixed 4`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  sorry

/-- Round trip, for fewer than `2^32` bytes. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 2 ^ 32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 s.length ++ s ++ tail) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
