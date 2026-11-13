import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt
import Proofs.Misc.Raw.Int.LenEnc

/-! Statements for `impl BytesRepr for LenEnc` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LenEnc::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.Usize.MAX]

/-- `LenEnc::SIZE` is `None`. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `LenEnc::serialize`: appends the length-encoded string. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr text.val).length ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ lenencStr text.val ⦄ := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  simp only [lenencStr, List.length_append] at h
  step as ⟨ i1, hi1 ⟩
  have hi1' : i1.val = text.length := by subst hi1; simp
  step with io.BufMutExt.put_lenenc_int_spec buf i1 (by rw [hi1']; scalar_tac) as ⟨ v, hv ⟩
  step as ⟨ w, hw ⟩
  simp [hw, hv, hi1', lenencStr]

private theorem deserialize_aux (buf : io.ParseBuf)
    (hfit : ∀ n : Nat, n < 2 ^ 64 → (checkedLenencInt buf.val).1 = some n → n ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenencStr buf.val ⦄ := by
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  cases r with
  | Err e =>
    simp only [okPart, Option.map_none] at hr
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart,
      checkedLenencStr, ← hr]
  | Ok val =>
    obtain ⟨i, _⟩ := val
    simp only [okPart, Option.map] at hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hfit' := hfit i.val (by scalar_tac) (by rw [← hr])
    step as ⟨ i1, hi1 ⟩
    have hi1' : i1.val = i.val := by
      subst hi1; apply UScalar.cast_val_mod_pow_of_inBounds_eq
      exact usize_lt_of_le_max hfit'
    step with io.ParseBuf.checked_eat_spec buf1 i1 as ⟨ o, buf2, ho ⟩
    simp only [checkedLenencStr, ← hr]
    split at ho
    · obtain ⟨ho1, ho2⟩ := ho
      cases o with
      | none => simp at ho1
      | some x =>
        simp at ho1
        rw [hi1'] at *
        simp [okPart, cowList, ho1, ho2, ‹i.val ≤ Slice.length buf1›]
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1 ho2
      rw [hi1'] at *
      simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, ‹¬ i.val ≤ Slice.length buf2›]

/-- `LenEnc::deserialize`: total; `checkedLenencStr` (with the lenenc quirk: `0xFB`/`0xFF` read as length 0, so as the empty string). Provided the length read fits in a `usize` (`hfit`; always true on the 64-bit target, `lenenc_fits_of_target64`). -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf)
    (hfit : ∀ n, (checkedLenencInt buf.val).1 = some n → n ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenencStr buf.val ⦄ := by
  apply WP.spec_mono (deserialize_aux buf (fun n _ hn => hfit n hn))
  intro x hx; exact hx

/-- Round trip: reads back the length-encoded string `s`. -/
theorem misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencStr s ++ tail) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  have hlen : s.length ≤ Usize.max := by
    have := buf.property
    have : buf.val.length = (lenencStr s ++ tail).length := by rw [h]
    simp [lenencStr] at this; scalar_tac
  have hc : checkedLenencInt buf.val = (some s.length, s ++ tail) := by
    rw [h]; simp only [lenencStr, List.append_assoc]
    exact PBUtil.checkedLenencInt_lenencInt _ _ (lt_two_pow_64_of_le_max hlen)
  have hs : checkedLenencStr buf.val = (some s, tail) := by
    rw [h]; unfold checkedLenencStr lenencStr
    rw [List.append_assoc, PBUtil.checkedLenencInt_lenencInt _ _ (lt_two_pow_64_of_le_max hlen)]
    simp
  apply WP.spec_mono (deserialize_aux buf (fun n _ hn => by simp [hc] at hn; omega))
  rintro ⟨r, rest⟩ hr
  simp only [hs, WP.uncurry'_pair, Prod.mk.injEq] at hr
  exact hr

end mysql_common
