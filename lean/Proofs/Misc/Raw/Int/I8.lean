import Defs

/-! Statements for `impl IntRepr for i8` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `i8::SIZE` is `Some(1)`. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE_eq :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE = some 1#usize := by
  sorry

/-- `i8::serialize`: appends `leBytesI 1 x.val`. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize_spec (x : I8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 1 x.val ⦄ := by
  sorry

/-- `i8::deserialize`: reads 1 byte. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1 ⦄ := by
  sorry

/-- `i8::deserialize` panics on fewer than 1 byte. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<i8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<i8>>` reads back what `RawInt::<i8>::serialize` writes. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.roundtrip (x : I8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 1 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
