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
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf = fail .panic := by
  unfold misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize
  exact PBUtil.bind_fail_left (io.ParseBuf.eat_i64_le_panics buf h)

/-- `buf.parse::<RawInt<LeI64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄ := by
  exact IntAndMisc.parse_rawint_take misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64 8#usize 8 (by simp [misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq]) rfl (·.val) (fun l => toSigned 64 (leNat l))
    (fun sub h => misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec sub h) buf

/-- Round trip: `parse::<RawInt<LeI64>>` reads back what `RawInt::<LeI64>::serialize` writes. -/
theorem misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄ := by
  exact IntAndMisc.rawint_roundtrip misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64 8 (·.val) (fun l => toSigned 64 (leNat l)) buf (misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec buf) _ tail
    (IntAndMisc.length_leBytesI 8 _) h _ (by
      rw [IntAndMisc.leNat_leBytesI, show 8 * 8 = 64 from rfl]
      exact IntAndMisc.toSigned_emod 64 (by norm_num) _ (by scalar_tac) (by scalar_tac))

end mysql_common
