import Defs

/-! Statements for `impl IntRepr for LeI16` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeI16::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE_eq :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE = some 2#usize := by
  sorry

/-- `LeI16::serialize`: appends `leBytesI 2 x.val`. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize_spec (x : I16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 2 x.val ⦄ := by
  sorry

/-- `LeI16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `LeI16::deserialize` panics on fewer than 2 bytes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeI16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeI16>>` reads back what `RawInt::<LeI16>::serialize` writes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.roundtrip (x : I16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
