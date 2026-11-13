import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeU32` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU32::SIZE` is `Some(4)`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 4#usize := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `LeU32::serialize`: appends `leBytes 4 x.val`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 x.val ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize
  exact IntAndMisc.put_u32_le_spec buf x h

/-- `LeU32::deserialize`: reads 4 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  step with io.ParseBuf.eat_u32_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeU32::deserialize` panics on fewer than 4 bytes. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf = fail .panic := by
  unfold misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  exact PBUtil.bind_fail_left (io.ParseBuf.eat_u32_le_panics buf h)

/-- `buf.parse::<RawInt<LeU32>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 4 bytes. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄ := by
  exact IntAndMisc.parse_rawint_take misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 4#usize 4 (by simp [misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq]) rfl (·.val) (leNat)
    (fun sub h => misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec sub h) buf

/-- Round trip: `parse::<RawInt<LeU32>>` reads back what `RawInt::<LeU32>::serialize` writes. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  exact IntAndMisc.rawint_roundtrip misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 4 (·.val) (leNat) buf (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) _ tail
    (PBUtil.length_leBytes 4 _) h _ (by
      rw [PBUtil.leNat_leBytes]; exact Nat.mod_eq_of_lt (by scalar_tac))

end mysql_common
