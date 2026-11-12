import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeI64` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeI64::SIZE` is `Some(8)`. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE = some 8#usize := by
  unfold misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE; rfl

/-- `LeI64::serialize`: appends `leBytesI 8 x.val`. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec (x : I64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 8 x.val ⦄ := by
  unfold misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize
  exact IntAndMisc.put_i64_le_spec buf x h

/-- `LeI64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize
  step with io.ParseBuf.eat_i64_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeI64::deserialize` panics on fewer than 8 bytes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.eat_i64_le_panics buf h)

/-- `buf.parse::<RawInt<LeI64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64 8#usize (by simp [misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (toSigned 64 (leNat (buf.val.take 8)))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeI64>>` reads back what `RawInt::<LeI64>::serialize` writes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 8 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytesI_take_drop 8 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytesI, show 8 * 8 = 64 from rfl]
  exact IntAndMisc.toSigned_emod 64 (by norm_num) _ (by scalar_tac) (by scalar_tac)

end mysql_common
