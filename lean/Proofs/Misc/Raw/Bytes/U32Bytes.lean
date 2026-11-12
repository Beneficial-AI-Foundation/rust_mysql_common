import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt
import Proofs.Defs.Lemmas

/-! Statements for `impl BytesRepr for U32Bytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `U32Bytes::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  unfold misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.U32.MAX, U32.rMax]

/-- `U32Bytes::SIZE` is `None`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `U32Bytes::serialize`: appends a little-endian `u32` length and the bytes, truncated to `u32::MAX` bytes (documented). -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + min text.length (2 ^ 32 - 1) ≤ Usize.max) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min text.length (2 ^ 32 - 1)) ++ text.val.take (2 ^ 32 - 1) ⦄ := by
  unfold misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  exact io.BufMutExt.put_u32_str_spec buf text h

/-- `U32Bytes::deserialize`: total; `checkedLenPrefixed 4`. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  unfold misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with io.ParseBuf.checked_eat_u32_str_spec buf as ⟨ o, buf1, ho ⟩
  cases o with
  | none => simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, ← ho]
  | some x => simp [okPart, cowList, ← ho]

/-- Round trip, for fewer than `2^32` bytes. -/
theorem misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 2 ^ 32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 s.length ++ s ++ tail) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  have hl : (leBytes 4 s.length).length = 4 := Defs.length_leBytes 4 s.length
  have hn : leNat (leBytes 4 s.length) = s.length := by
    rw [Defs.leNat_leBytes]; exact Nat.mod_eq_of_lt (by omega)
  have hc : checkedLenPrefixed 4 buf.val = (some s, tail) := by
    simp [checkedLenPrefixed, readLE, h, hl, hn]
  apply WP.spec_mono (misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [hc, WP.uncurry'_pair, Prod.mk.injEq] at hr
  exact hr

end mysql_common
