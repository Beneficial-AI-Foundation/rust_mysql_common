import Proofs.Util.IntAndMisc
import Proofs.Io.BufMutExt

/-! Statements for `impl IntRepr for LenEnc` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `LenEnc::SIZE` is `None` (variable length). -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = none := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE; rfl

/-- `LenEnc::serialize`: appends the length-encoded integer. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt x.val).length ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄ := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize
  exact io.BufMutExt.put_lenenc_int_spec buf x h

/-- `LenEnc::deserialize`: total; `checked_eat_lenenc_int` (so `checkedLenencInt`, with its `0xFB`/`0xFF` quirk), `None` turned into an error. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = checkedLenencInt buf.val ⦄ := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
  step with io.ParseBuf.checked_eat_lenenc_int_spec as ⟨ o, rest, ho ⟩
  cases o with
  | none => step*; simpa [okPart] using ho
  | some v => simpa [okPart] using ho

/-- `buf.parse::<RawInt<LenEnc>>(())`: total; `checkedLenencInt` (`SIZE` is `None`, so this is `deserialize`). -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ((okPart r).map (·.1.val), rest.val) = checkedLenencInt buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ buf () (by simp [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE, misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq])]
  have := IntAndMisc.rawint_deserialize_spec misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun o rest => (o.map (·.val), rest.val) = checkedLenencInt buf.val) (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map, Function.comp_def] using h1

/-- Round trip: `parse::<RawInt<LenEnc>>` reads back what `RawInt::<LenEnc>::serialize` writes, for every `u64`. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1) = some x ∧ rest.val = tail ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ buf () (by simp [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE, misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq])]
  have := IntAndMisc.rawint_deserialize_spec misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun o rest => o = some x ∧ rest.val = tail) (by
      change misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄
      unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize
      step with io.ParseBuf.checked_eat_lenenc_int_roundtrip x tail buf h as ⟨ o, rest, ho, hr ⟩
      subst ho
      simp [okPart, hr])
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa using h1

end mysql_common
