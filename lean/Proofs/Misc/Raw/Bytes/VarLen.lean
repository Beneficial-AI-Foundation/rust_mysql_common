import Defs

/-! Statements for `impl BytesRepr for VarLen` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `VarLen::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  sorry

/-- `VarLen::SIZE` is `None`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  sorry

/-- `VarLen::serialize`: **Bug (format mismatch).** Appends the length as a *length-encoded integer*
    (`put_lenenc_int`), not as a JSONB varlen integer, which is what `deserialize` reads. The two
    agree only for lengths below 128; for `128 ≤ len < 251` the lenenc byte `len` has bit 7 set
    and is read as an unfinished varlen. No `u32::MAX` truncation either. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 9 + text.length ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ lenencInt text.length ++ text.val ⦄ := by
  sorry

/-- `VarLen::deserialize`: total; a JSONB-varlen length then that many bytes (`jsonbVarLenStrRead`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = jsonbVarLenStrRead buf.val ⦄ := by
  sorry

/-- Round trip of `serialize` holds only for strings shorter than 128 bytes (see the bug on `serialize`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 128) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
