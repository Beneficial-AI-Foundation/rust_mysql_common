import Proofs.Util.IntAndMisc
import Proofs.Io.BufMutExt

/-! Statements for `impl IntRepr for LeU24` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU24::SIZE` is `Some(3)`. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 3#usize := by
  unfold misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `LeU24::serialize`: appends `leBytes 3 x.val`. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄ := by
  unfold misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize
  exact io.BufMutExt.put_u24_le_spec buf x h

/-- `LeU24::deserialize`: reads 3 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3 ⦄ := by
  unfold misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  step with io.ParseBuf.eat_u24_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeU24::deserialize` panics on fewer than 3 bytes. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  exact PBUtil.not_spec_bind_left (io.ParseBuf.eat_u24_le_panics buf h)

/-- `buf.parse::<RawInt<LeU24>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 3 bytes. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32 3#usize (by simp [misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (leNat (buf.val.take 3))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeU24>>` reads back what `RawInt::<LeU24>::serialize` writes. A `u32` above `2^24 - 1` loses its top byte. -/
theorem misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 3 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 24) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 3 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytes_take_drop 3 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [PBUtil.leNat_leBytes]

end mysql_common
