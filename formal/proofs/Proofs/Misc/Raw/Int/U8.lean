import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for u8` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `u8::SIZE` is `Some(1)`. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE = some 1#usize := by
  unfold U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE; rfl

/-- `u8::serialize`: appends `[x]`. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec (x : U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [x] ⦄ := by
  unfold U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize
  exact IntAndMisc.put_u8_spec buf x h

/-- `u8::deserialize`: reads 1 byte. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄ := by
  unfold U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize
  step with io.ParseBuf.eat_u8_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `u8::deserialize` panics on fewer than 1 byte. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf = fail .panic := by
  unfold U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize
  exact PBUtil.bind_fail_left (io.ParseBuf.eat_u8_panics buf h)

/-- `buf.parse::<RawInt<u8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  exact IntAndMisc.parse_rawint_take U8.Insts.Mysql_commonMiscRawIntIntReprU8 1#usize 1 (by simp [U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq]) rfl (·.val) leNat
    (fun sub h => U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec sub h) buf

/-- Round trip: `parse::<RawInt<u8>>` reads back what `RawInt::<u8>::serialize` writes. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.roundtrip (x : U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = [x] ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  exact IntAndMisc.rawint_roundtrip U8.Insts.Mysql_commonMiscRawIntIntReprU8 1 (·.val) leNat buf (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) _ tail rfl h _
    (by simp [leNat])

end mysql_common
