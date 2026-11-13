import Proofs.Util.IntAndMisc
import Proofs.Io.BufMutExt

/-! Statements for `impl IntRepr for LeU56` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LeU56::SIZE` is `Some(7)`. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 7#usize := by
  unfold misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE; rfl

/-- `LeU56::serialize`: appends `leBytes 7 x.val`. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 ≤ Usize.max) :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 7 x.val ⦄ := by
  unfold misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize
  exact io.BufMutExt.put_u56_le_spec buf x h

/-- `LeU56::deserialize`: reads 7 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
  step with io.ParseBuf.eat_u56_le_spec as ⟨ i, rest, hi, hr ⟩
  simp [okPart, hi, hr]

/-- `LeU56::deserialize` panics on fewer than 7 bytes. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf = fail .panic := by
  unfold misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
  exact PBUtil.bind_fail_left (io.ParseBuf.eat_u56_le_panics buf h)

/-- `buf.parse::<RawInt<LeU56>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 7 bytes. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 7 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else okPart r = none ∧ rest = buf ⦄ := by
  exact IntAndMisc.parse_rawint_take misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64 7#usize 7 (by simp [misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq]) rfl (·.val) (leNat)
    (fun sub h => misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec sub h) buf

/-- Round trip: `parse::<RawInt<LeU56>>` reads back what `RawInt::<LeU56>::serialize` writes. A `u64` above `2^56 - 1` loses its top byte. -/
theorem misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 7 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 56) ∧ rest.val = tail ⦄ := by
  exact IntAndMisc.rawint_roundtrip misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64 7 (·.val) (leNat) buf (misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf) _ tail
    (PBUtil.length_leBytes 7 _) h _ (by
      rw [PBUtil.leNat_leBytes])

end mysql_common
