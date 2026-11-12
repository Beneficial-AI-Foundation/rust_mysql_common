import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impl BytesRepr for NullBytes` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `NullBytes::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max := by
  unfold misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.Usize.MAX]

/-- `NullBytes::SIZE` is `None`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `NullBytes::serialize`: appends the bytes before the first `0` (all of them if there is none), then a `0`: a string containing `0` is silently truncated. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + text.length ≤ Usize.max) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ beforeZero text.val ++ [byte 0] ⦄ := by
  unfold misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  step with position_of_zero_spec as ⟨ o, ho ⟩
  have hle := beforeZero_length_le text.val
  split at ho
  · rename_i hc
    cases o with
    | none => simp at ho
    | some i =>
      simp at ho
      simp only
      step as ⟨ s, hs1, hs2 ⟩
      step as ⟨ v, hv ⟩
      step as ⟨ w, hw ⟩
      simp [hw, hv, hs1, List.slice, ho, take_beforeZero_length]; rfl
  · rename_i hc
    subst ho
    simp only
    step as ⟨ s, hs1, hs2 ⟩
    step as ⟨ v, hv ⟩
    step as ⟨ w, hw ⟩
    simp [hw, hv, hs1, List.slice, beforeZero_eq_self _ hc]; rfl

/-- `NullBytes::deserialize`: total; the bytes before the first `0`, consuming the `0`; an error (its kind is not stated: `io::Error` is opaque; documented as `InvalidData`) with the buffer unchanged if there is no `0`. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      if ∃ b ∈ buf.val, b.val = 0 then
        (okPart r).map cowList = some (beforeZero buf.val) ∧
        rest.val = buf.val.drop ((beforeZero buf.val).length + 1)
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with position_of_zero_spec as ⟨ o, ho ⟩
  split at ho
  · rename_i hc
    have hlt := beforeZero_length_lt _ hc
    cases o with
    | none => simp at ho
    | some i =>
      simp at ho
      simp only
      step with io.ParseBuf.eat_spec buf i (by scalar_tac) as ⟨ out, buf1, h1, h2 ⟩
      step with io.ParseBuf.skip_spec buf1 1#usize (by simp [Slice.length, h2]; omega) as ⟨ buf2, h3 ⟩
      simp [hc, okPart, cowList, h1, h3, h2, ho, take_beforeZero_length, List.drop_drop]
  · rename_i hc
    subst ho
    simp [hc, okPart, misc.io_error_msg]

/-- Round trip, for strings without a `0` byte. -/
theorem misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : ∀ b ∈ s, b.val ≠ 0) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = s ++ [byte 0] ++ tail) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  have hs' : ∀ b ∈ s, b.val ≠ 0 := hs
  have hz : ∃ b ∈ buf.val, b.val = 0 := ⟨byte 0, by simp [h], by simp [byte]; rfl⟩
  have hb : beforeZero buf.val = s := by rw [h]; simpa using beforeZero_append_zero s tail hs'
  apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [hz, ↓reduceIte, hb, WP.uncurry'_pair] at hr
  refine ⟨hr.1, ?_⟩
  rw [hr.2, h]; simp

end mysql_common
