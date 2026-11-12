import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt
import Proofs.Misc.Raw.Int.U8

/-! Statements for `impl BytesRepr for U8Bytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `U8Bytes::MAX_LEN`: `255`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 255 ⦄ := by
  unfold misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.U8.MAX, U8.rMax]

/-- `U8Bytes::SIZE` is `None`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `U8Bytes::serialize`: appends a `u8` length and the bytes, truncated to 255 bytes (documented). -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + min text.length 255 ≤ Usize.max) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ byte (min text.length 255) :: text.val.take 255 ⦄ := by
  unfold misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  exact io.BufMutExt.put_u8_str_spec buf text h

/-- `U8Bytes::deserialize`: total; `checkedLenPrefixed 1`. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  unfold misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  split at hr
  · obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      simp [okPart] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨i, _⟩ := val
      simp only at hr1 ⊢
      step as ⟨ i1, hi1 ⟩
      have hi1' : i1.val = i.val := by subst hi1; simp
      step with io.ParseBuf.checked_eat_spec buf1 i1 as ⟨ o, buf2, ho ⟩
      have hlen : buf1.length = buf.length - 1 := by simp [Slice.length, hr2]
      simp only [checkedLenPrefixed, readLE, *, ↓reduceIte]
      split at ho
      · obtain ⟨ho1, ho2⟩ := ho
        cases o with
        | none => simp at ho1
        | some x =>
          simp at ho1
          simp [okPart, cowList, ho1, ho2, hr2, ← hr1, hi1']
          simp [Slice.length] at *; omega
      · obtain ⟨ho1, ho2⟩ := ho
        subst ho1 ho2
        simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, hr2]
        simp [Slice.length] at *; omega
  · obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hr1
    | Err e =>
      subst hr2
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        okPart, checkedLenPrefixed, readLE, *]

/-- Round trip, for at most 255 bytes. -/
theorem misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length ≤ 255) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte s.length :: s ++ tail) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  have hb : (byte s.length).val = s.length := by
    show (BitVec.ofNat 8 s.length).toNat = s.length
    simp; omega
  have hc : checkedLenPrefixed 1 buf.val = (some s, tail) := by
    simp [checkedLenPrefixed, readLE, h, leNat, hb]
  apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [hc, WP.uncurry'_pair, Prod.mk.injEq] at hr
  exact hr

end mysql_common
