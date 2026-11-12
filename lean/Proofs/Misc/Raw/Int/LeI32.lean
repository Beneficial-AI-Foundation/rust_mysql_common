import Defs

/-! Statements for `impl IntRepr for LeI32` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeI32::SIZE` is `Some(4)`. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE = some 4#usize := by
  sorry

/-- `LeI32::serialize`: appends `leBytesI 4 x.val`. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec (x : I32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 4 x.val ⦄ := by
  sorry

/-- `LeI32::deserialize`: reads 4 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `LeI32::deserialize` panics on fewer than 4 bytes. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeI32>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 4 bytes. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeI32>>` reads back what `RawInt::<LeI32>::serialize` writes. -/
theorem misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip (x : I32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 4 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
