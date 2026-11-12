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
    ¬ U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf ⦃ _ => True ⦄ := by
  unfold U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.eat_u8_panics buf h)

/-- `buf.parse::<RawInt<u8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint U8.Insts.Mysql_commonMiscRawIntIntReprU8 1#usize (by simp [U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (leNat (buf.val.take 1))) (by
      intro sub hsub hl
      apply spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<u8>>` reads back what `RawInt::<u8>::serialize` writes. -/
theorem U8.Insts.Mysql_commonMiscRawIntIntReprU8.roundtrip (x : U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = [x] ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  apply spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 1 ≤ buf.length := by simp [Slice.length, h]
  simp only [hl, ↓reduceIte, h, List.singleton_append, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; simp [leNat]

end mysql_common
