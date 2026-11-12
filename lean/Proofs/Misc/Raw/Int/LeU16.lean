import Defs

/-! Statements for `impl IntRepr for LeU16` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeU16::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE = some 2#usize := by
  sorry

/-- `LeU16::serialize`: appends `leBytes 2 x.val`. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec (x : U16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.val ⦄ := by
  sorry

/-- `LeU16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer; `parse` (below) checks. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeU16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeU16>>` reads back what `RawInt::<LeU16>::serialize` writes. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.roundtrip (x : U16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
