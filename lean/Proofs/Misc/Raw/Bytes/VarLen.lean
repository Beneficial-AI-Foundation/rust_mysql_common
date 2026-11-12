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
    agree only for lengths below 128. From 128 on the first length byte has bit 7 set, so
    `deserialize` takes the following byte(s) as part of the length and can silently read a wrong
    length: e.g. a 200-byte string starting with `'a'` is read as having length 12488
    (`Defs.jsonbVarLenRead_lenencInt_misread`); see `roundtrip_fails`. No `u32::MAX` truncation
    either. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt text.length).length + text.length ≤ Usize.max) :
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

/-- **Bug (format mismatch).** For every length `≥ 128`, `deserialize` does not read back what
    `serialize` writes: it fails or leaves a different rest. (From 128 to 250 the single lenenc
    byte has bit 7 set; from 251 on the lenenc header is `0xFC`/`0xFD`/`0xFE` plus 2/3/8 bytes, and
    the JSONB reader never stops after exactly the header with the right value: for `0xFC`/`0xFD`
    the equations have no solution, and the 9-byte `0xFE` header is longer than the 5 bytes the
    JSONB reader accepts.) -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip_fails (s tail : List U8) (hs : 128 ≤ s.length ∧ s.length < 2 ^ 64)
    (buf : io.ParseBuf) (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => ((okPart r).map cowList, rest.val) ≠ (some s, tail) ⦄ := by
  sorry

end mysql_common
