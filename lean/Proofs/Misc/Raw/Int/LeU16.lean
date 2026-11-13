import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeU16` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU16::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE = some 2#usize := by
  unfold misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE; rfl

/-- `LeU16::serialize`: appends `leBytes 2 x.val`. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec (x : U16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.val ⦄ := by
  unfold misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize
  exact IntAndMisc.put_u16_le_spec buf x h

/-- `LeU16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize
  step with io.ParseBuf.eat_u16_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeU16::deserialize` panics on fewer than 2 bytes. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize buf = fail .panic := by
  unfold misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize
  exact PBUtil.bind_fail_left (io.ParseBuf.eat_u16_le_panics buf h)

/-- `buf.parse::<RawInt<LeU16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  exact IntAndMisc.parse_rawint_take misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 2#usize 2 (by simp [misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq]) rfl (·.val) leNat
    (fun sub h => misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec sub h) buf

/-- Round trip: `parse::<RawInt<LeU16>>` reads back what `RawInt::<LeU16>::serialize` writes. -/
theorem misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.roundtrip (x : U16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  exact IntAndMisc.rawint_roundtrip misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 2 (·.val) leNat buf (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) _ tail
    (PBUtil.length_leBytes 2 _) h _ (by rw [PBUtil.leNat_leBytes]; exact Nat.mod_eq_of_lt (by scalar_tac))

end mysql_common
