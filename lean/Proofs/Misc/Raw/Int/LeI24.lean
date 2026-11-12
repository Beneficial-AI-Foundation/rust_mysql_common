import Defs

/-! Statements for `impl IntRepr for LeI24` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeI24::SIZE` is `Some(3)`. -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE = some 3#usize := by
  sorry

/-- `LeI24::serialize`: appends `leBytesI 3 x.val`. -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec (x : I32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 3 x.val ⦄ := by
  sorry

/-- `LeI24::deserialize`: reads 3 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `LeI24::deserialize` panics on fewer than 3 bytes. -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawInt<LeI24>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 3 bytes. -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (·.1.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LeI24>>` reads back what `RawInt::<LeI24>::serialize` writes. **Not a round trip for negative values**: the reader (`eat_i24_le`) zero-extends, so `-1` comes back as `16777215` (and any `x` comes back as `x mod 2^24`, in `[0, 2^24)`). -/
theorem misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip (x : I32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 3 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 24) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
