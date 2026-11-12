import Proofs.Util.IntAndMisc

/-! Statements for `impl IntRepr for LeI56` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeI56::SIZE` is `Some(7)`. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE = some 7#usize := by
  unfold misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE; rfl

/-- `LeI56::serialize`: appends `leBytesI 7 x.val`. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec (x : I64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 ≤ Usize.max) :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 7 x.val ⦄ := by
  unfold misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize
  exact io.BufMutExt.put_i56_le_spec buf x h

/-- `LeI56::deserialize`: reads 7 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize
  step with io.ParseBuf.eat_i56_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeI56::deserialize` panics on fewer than 7 bytes. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.eat_i56_le_panics buf h)

/-- `buf.parse::<RawInt<LeI56>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 7 bytes. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 7 ≤ buf.length then
        (okPart r).map (·.1.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_rawint misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64 7#usize (by simp [misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq]) buf
    (fun o => o.map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int))) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip: `parse::<RawInt<LeI56>>` reads back what `RawInt::<LeI56>::serialize` writes. **Not a round trip for negative values**: the reader (`eat_i56_le`) zero-extends, so any `x` comes back as `x mod 2^56`, in `[0, 2^56)`. -/
theorem misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 7 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 56) ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 7 ≤ buf.length := by simp [Slice.length, h]
  obtain ⟨h1, h2⟩ := IntAndMisc.leBytesI_take_drop 7 x.val tail
  simp only [hl, ↓reduceIte, h, h1, h2] at hr
  refine ⟨?_, hr.2⟩
  rw [hr.1]; refine congrArg some ?_
  rw [IntAndMisc.leNat_leBytesI, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]

end mysql_common
