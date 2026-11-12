import Proofs.Util.IntAndMisc
import Proofs.Misc.Raw.Int.LeU16

/-! Statements for `impl IntRepr for LeU32UpperHalf` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU32UpperHalf::SIZE` is `Some(2)`. -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 2#usize := by
  unfold misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE; rfl

/-- `LeU32UpperHalf::serialize`: appends `leBytes 2 (x.val / 2 ^ 16)`. -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 (x.val / 2 ^ 16) ⦄ := by
  unfold misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize
  step*
  have hv : i1.val = x.val / 2 ^ 16 := by
    rw [i1_post, UScalar.cast_val_eq, i_post, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by have := x.hBounds; simp [UScalarTy.numBits] at *; omega)
  apply spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec i1 buf h)
  intro b hb
  rw [hb, hv]

/-- `LeU32UpperHalf::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2) * 2 ^ 16) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec as ⟨ r, rest, hr, hrest ⟩
  cases r with
  | Ok v =>
    step*
    simp only [okPart, Option.map_some, Option.some.injEq] at hr ⊢
    refine ⟨?_, hrest⟩
    have hv : i.val = v.val := by
      rw [i_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by scalar_tac)
    have hb : v.val < 65536 := by scalar_tac
    have : i1.val = v.val * 65536 := by
      rw [i1_post, hv, Nat.shiftLeft_eq]
      simp only [U32.size, U32.numBits, UScalarTy.numBits]
      omega
    rw [this, hr]; norm_num
  | Err e => simp [okPart] at hr

/-- `LeU32UpperHalf::deserialize` panics on fewer than 2 bytes. -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize
  exact IntAndMisc.not_spec_bind (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_panics buf h)

/-- `buf.parse::<RawInt<LeU32UpperHalf>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2) * 2 ^ 16) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32 2#usize (by simp [misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (leNat (buf.val.take 2) * 2 ^ 16)) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeU32UpperHalf>>` reads back what `RawInt::<LeU32UpperHalf>::serialize` writes. (The lower half of the `u32` is not stored, by design.) -/
theorem misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 (x.val / 2 ^ 16) ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val / 2 ^ 16 * 2 ^ 16) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 2 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytes_take_drop 2 (x.val / 2 ^ 16) tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytes', Nat.mod_eq_of_lt]
  have := x.hBounds; simp [UScalarTy.numBits] at *; omega

end mysql_common
