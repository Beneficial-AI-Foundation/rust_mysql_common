import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeI16` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeI16::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE_eq :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE = some 2#usize := by
  unfold misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE; rfl

/-- `LeI16::serialize`: appends `leBytesI 2 x.val`. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize_spec (x : I16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 2 x.val ⦄ := by
  unfold misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize
  exact IntAndMisc.put_i16_le_spec buf x h

/-- `LeI16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize
  step with io.ParseBuf.eat_i16_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeI16::deserialize` panics on fewer than 2 bytes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.eat_i16_le_panics buf h)

/-- `buf.parse::<RawInt<LeI16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16 2#usize (by simp [misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (toSigned 16 (leNat (buf.val.take 2)))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeI16>>` reads back what `RawInt::<LeI16>::serialize` writes. -/
theorem misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.roundtrip (x : I16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 2 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytesI_take_drop 2 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytesI, show 8 * 2 = 16 from rfl]
  exact IntAndMisc.toSigned_emod 16 (by norm_num) _ (by scalar_tac) (by scalar_tac)

end mysql_common
