import Defs

/-! Statements for `impl BytesRepr for FixedLengthText<LEN>` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FixedLengthText<LEN>::MAX_LEN`: `LEN`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN L = L := by
  sorry

/-- `FixedLengthText<LEN>::SIZE` is `Some(LEN)`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE L = some L := by
  sorry

/-- `FixedLengthText<LEN>::serialize`: appends exactly `LEN` bytes: the text, truncated or right-padded with `0x00` (documented). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (L : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + L.val ≤ Usize.max) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize L text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ⦄ := by
  sorry

/-- `FixedLengthText<LEN>::deserialize`: the next `LEN` bytes, padding included. Unchecked (`SIZE` is `Some(LEN)`, so it uses `eat`): panics on a shorter buffer; `parse` checks. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (L : Usize) (buf : io.ParseBuf) (h : L.val ≤ buf.length) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ r rest =>
      (okPart r).map cowList = some (buf.val.take L.val) ∧ rest.val = buf.val.drop L.val ⦄ := by
  sorry

end mysql_common
