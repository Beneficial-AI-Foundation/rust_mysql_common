import Defs

/-! Statements for `impl IntRepr for LeU24` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeU24::SIZE` is `Some(3)`. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 3#usize := by
  sorry

/-- `LeU24::serialize`: appends `leBytes 3 x.val`. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄ := by
  sorry

/-- `LeU24::deserialize`: reads 3 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `LeU24::deserialize` panics on fewer than 3 bytes. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeU24>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 3 bytes. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeU24>>` reads back what `RawInt::<LeU24>::serialize` writes. A `u32` above `2^24 - 1` loses its top byte. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 3 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 24) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
