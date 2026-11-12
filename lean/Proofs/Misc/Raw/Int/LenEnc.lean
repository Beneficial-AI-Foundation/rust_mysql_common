import Defs

/-! Statements for `impl IntRepr for LenEnc` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LenEnc::SIZE` is `None` (variable length). -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = none := by
  sorry

/-- `LenEnc::serialize`: appends the length-encoded integer. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 9 ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄ := by
  sorry

/-- `LenEnc::deserialize`: total; `checked_eat_lenenc_int` (so `checkedLenencInt`, with its `0xFB`/`0xFF` quirk), `None` turned into an error. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = checkedLenencInt buf.val ⦄ := by
  sorry

/-- Round trip: `parse::<RawInt<LenEnc>>` reads back what `RawInt::<LenEnc>::serialize` writes, for every `u64`. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1) = some x ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
