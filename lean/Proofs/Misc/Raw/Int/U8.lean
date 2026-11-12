import Defs

/-! Statements for `impl IntRepr for u8` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `u8::SIZE` is `Some(1)`. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE = some 1#usize := by
  sorry

/-- `u8::serialize`: appends `[x]`. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec (x : U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [x] ⦄ := by
  sorry

/-- `u8::deserialize`: reads 1 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer; `parse` (below) checks. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄ := by
  sorry

/-- `buf.parse::<RawInt<u8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 bytes. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<u8>>` reads back what `RawInt::<u8>::serialize` writes. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.roundtrip (x : U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = [x] ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
