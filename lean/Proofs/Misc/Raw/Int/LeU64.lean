import Defs

/-! Statements for `impl IntRepr for LeU64` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeU64::SIZE` is `Some(8)`. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 8#usize := by
  sorry

/-- `LeU64::serialize`: appends `leBytes 8 x.val`. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 x.val ⦄ := by
  sorry

/-- `LeU64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `LeU64::deserialize` panics on fewer than 8 bytes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeU64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeU64>>` reads back what `RawInt::<LeU64>::serialize` writes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
