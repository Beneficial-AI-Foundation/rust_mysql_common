import Defs

/-! Statements for `impl BytesRepr for U8Bytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `U8Bytes::MAX_LEN`: `255`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 255 ⦄ := by
  sorry

/-- `U8Bytes::SIZE` is `None`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  sorry

/-- `U8Bytes::serialize`: appends a `u8` length and the bytes, truncated to 255 bytes (documented). -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + text.length ≤ Usize.max) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ byte (min text.length 255) :: text.val.take 255 ⦄ := by
  sorry

/-- `U8Bytes::deserialize`: total; `checkedLenPrefixed 1`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  sorry

/-- Round trip, for at most 255 bytes. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length ≤ 255) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte s.length :: s ++ tail) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
