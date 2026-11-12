import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeU64` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU64::SIZE` is `Some(8)`. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 8#usize := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE; rfl

/-- `LeU64::serialize`: appends `leBytes 8 x.val`. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 x.val ⦄ := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize
  exact IntAndMisc.put_u64_le_spec buf x h

/-- `LeU64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
  step with io.ParseBuf.eat_u64_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeU64::deserialize` panics on fewer than 8 bytes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.eat_u64_le_panics buf h)

/-- `buf.parse::<RawInt<LeU64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 8#usize (by simp [misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (leNat (buf.val.take 8))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeU64>>` reads back what `RawInt::<LeU64>::serialize` writes. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 8 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytes_take_drop 8 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytes']; exact Nat.mod_eq_of_lt (by scalar_tac)

end mysql_common
