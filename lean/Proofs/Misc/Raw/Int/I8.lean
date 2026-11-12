import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for i8` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `i8::SIZE` is `Some(1)`. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE_eq :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE = some 1#usize := by
  unfold I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE; rfl

/-- `i8::serialize`: appends `leBytesI 1 x.val`. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize_spec (x : I8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 1 x.val ⦄ := by
  unfold I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize
  exact IntAndMisc.put_i8_spec buf x h

/-- `i8::deserialize`: reads 1 byte. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1 ⦄ := by
  unfold I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize
  step with io.ParseBuf.eat_i8_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `i8::deserialize` panics on fewer than 1 byte. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ _ => True ⦄ := by
  unfold I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize
  exact PBUtil.not_spec_bind_left (io.ParseBuf.eat_i8_panics buf h)

/-- `buf.parse::<RawInt<i8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint I8.Insts.Mysql_commonMiscRawIntIntReprI8 1#usize (by simp [I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (toSigned 8 (leNat (buf.val.take 1)))) (by
      intro sub hsub hl
      apply spec_mono (I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<i8>>` reads back what `RawInt::<i8>::serialize` writes. -/
theorem I8.Insts.Mysql_commonMiscRawIntIntReprI8.roundtrip (x : I8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 1 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  apply spec_mono (I8.Insts.Mysql_commonMiscRawIntIntReprI8.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 1 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytesI_take_drop 1 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytesI, show 8 * 1 = 8 from rfl]
  exact IntAndMisc.toSigned_emod 8 (by norm_num) _ (by scalar_tac) (by scalar_tac)

end mysql_common
