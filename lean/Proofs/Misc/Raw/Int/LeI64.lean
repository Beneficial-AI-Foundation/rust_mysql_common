import Defs

/-! Statements for `impl IntRepr for LeI64` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeI64::SIZE` is `Some(8)`. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE = some 8#usize := by
  sorry

/-- `LeI64::serialize`: appends `leBytesI 8 x.val`. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec (x : I64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 8 x.val ⦄ := by
  sorry

/-- `LeI64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `LeI64::deserialize` panics on fewer than 8 bytes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeI64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeI64>>` reads back what `RawInt::<LeI64>::serialize` writes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
