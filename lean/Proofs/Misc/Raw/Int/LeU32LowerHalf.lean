import Proofs.Util.IntAndMisc
import Proofs.Misc.Raw.Int.LeU16

/-! Statements for `impl IntRepr for LeU32LowerHalf` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU32LowerHalf::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 2#usize := by
  unfold misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `LeU32LowerHalf::serialize`: appends `leBytes 2 x.val`. -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.val ⦄ := by
  unfold misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize
  step*
  have hv : i1.val = x.val % 2 ^ (8 * 2) := by
    rw [i1_post, UScalar.cast_val_eq, i_post]
    simp only [UScalar.val_and]
    rw [show (65535#u32).val = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp
  apply spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec i1 buf h)
  intro b hb
  rw [hb, hv, IntAndMisc.leBytes_mod]

/-- `LeU32LowerHalf::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec as ⟨ r, rest, hr, hrest ⟩
  cases r with
  | Ok v =>
    step*
    simp only [okPart, Option.map_some, Option.some.injEq] at hr ⊢
    refine ⟨?_, hrest⟩
    rw [i_post, UScalar.cast_val_eq, ← hr]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  | Err e => simp [okPart] at hr

/-- `LeU32LowerHalf::deserialize` panics on fewer than 2 bytes. -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  exact IntAndMisc.not_spec_bind (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_panics buf h)

/-- `buf.parse::<RawInt<LeU32LowerHalf>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32 2#usize (by simp [misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (leNat (buf.val.take 2))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeU32LowerHalf>>` reads back what `RawInt::<LeU32LowerHalf>::serialize` writes. (The upper half of the `u32` is not stored, by design.) -/
theorem misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 16) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 2 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytes_take_drop 2 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytes']

end mysql_common
