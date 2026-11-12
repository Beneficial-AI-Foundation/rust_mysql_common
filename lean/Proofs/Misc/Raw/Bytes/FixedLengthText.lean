import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Bytes.RawBytes

/-! Statements for `impl BytesRepr for FixedLengthText<LEN>` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FixedLengthText<LEN>::MAX_LEN`: `LEN`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN L = L := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN; rfl

/-- `FixedLengthText<LEN>::SIZE` is `Some(LEN)`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE L = some L := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

private theorem serialize_loop_spec (iter : core.ops.range.Range Usize) (buf : alloc.vec.Vec U8)
    (h : buf.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_loop iter buf
      ⦃ v => v.val = buf.val ++ List.replicate (iter.end.val - iter.start.val) 0#u8 ⦄ := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_loop
  apply loop.spec_decr_nat (fun p => p.1.end.val - p.1.start.val)
    (fun p => p.2.length + (p.1.end.val - p.1.start.val) ≤ Usize.max ∧
      p.2.val ++ List.replicate (p.1.end.val - p.1.start.val) 0#u8 =
        buf.val ++ List.replicate (iter.end.val - iter.start.val) 0#u8)
  · rintro ⟨it, b⟩ ⟨hb1, hb2⟩
    simp only at hb1 hb2
    unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_loop.body
    step as ⟨ o, it1, ho, he ⟩
    split at ho
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1
      simp only
      step as ⟨ b1, hb ⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [he] at *; scalar_tac
      · rw [← hb2, hb, he, ho2]
        obtain ⟨k, hk⟩ : ∃ k, it.end.val - it.start.val = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
        rw [hk, show it.end.val - (it.start.val + 1) = k by omega, List.replicate_succ]
        simp
      · rw [he, ho2]; omega
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1
      simp only [WP.spec_ok]
      rw [← hb2, show it.end.val - it.start.val = 0 by omega]
      simp
  · exact ⟨h, rfl⟩

/-- `FixedLengthText<LEN>::serialize`: appends exactly `LEN` bytes: the text, truncated or right-padded with `0x00` (documented). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (L : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + L.val ≤ Usize.max) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize L text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ⦄ := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  step as ⟨ len, hlen ⟩
  step as ⟨ s, hs1, hs2 ⟩
  step as ⟨ v, hv ⟩
  step as ⟨ i1, hi1 ⟩
  step with serialize_loop_spec { start := 0#usize, «end» := i1 } v (by simp [hv, Slice.length] at *; scalar_tac) as ⟨ w, hw ⟩
  simp [hw, hv, hs1, hlen, hi1, List.slice, byte]
  congr 1
  rcases Nat.le_total L.val text.val.length with hh | hh
  · simp [Nat.min_eq_left hh]
  · simp [Nat.min_eq_right hh, List.take_of_length_le hh]

/-- `FixedLengthText<LEN>::deserialize`: the next `LEN` bytes, padding included. Unchecked (`SIZE` is `Some(LEN)`, so it uses `eat`): panics on a shorter buffer (`deserialize_panics`); `parse` checks (`parse_rawbytes_spec`). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (L : Usize) (buf : io.ParseBuf) (h : L.val ≤ buf.length) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ r rest =>
      (okPart r).map cowList = some (buf.val.take L.val) ∧ rest.val = buf.val.drop L.val ⦄ := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  simp only [misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq]
  step with io.ParseBuf.eat_spec buf L h as ⟨ s, rest, hs, hr ⟩
  simp [okPart, cowList, hs, hr]

/-- `FixedLengthText<LEN>::deserialize` panics on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_panics (L : Usize) (buf : io.ParseBuf) (h : buf.length < L.val) :
    ¬ misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ _ => True ⦄ := by
  unfold misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  simp only [misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq]
  intro hc
  exact io.ParseBuf.eat_panics buf L h (spec_of_bind _ _ _ hc)

/-- `buf.parse::<RawBytes<FixedLengthText<LEN>>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.parse_rawbytes_spec (L : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      if L.val ≤ buf.length then
        (okPart r).map (fun rb => cowList rb.1) = some (buf.val.take L.val) ∧
        rest.val = buf.val.drop L.val
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs : (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)).SIZE = ok (some L) := by
    simp only [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq]
  split
  · rename_i hl
    apply WP.spec_mono (io.ParseBuf.parse_of_size _ buf () L hs hl
      (fun o => o.map (fun rb => cowList rb.1) = some (buf.val.take L.val)) ?_)
    · rintro ⟨r, rest⟩ hr; exact hr
    · intro sub hsub
      have hsl : L.val ≤ sub.length := by simp [Slice.length, hsub]; omega
      apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () sub
        (fun o _ => o = some (buf.val.take L.val))
      apply WP.spec_mono (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec L sub hsl)
      rintro ⟨r, rest⟩ hr
      simp only [WP.uncurry'_pair] at hr ⊢
      rw [hr.1, hsub]; simp
  · rename_i hl
    exact io.ParseBuf.parse_of_size_short _ buf () L hs (by omega)

/-- Round trip through `parse::<RawBytes<FixedLengthText<LEN>>>`: what `serialize` writes comes back padded/truncated to exactly `LEN` bytes (so it is the original text iff the text has `LEN` bytes). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (L : Usize) (text tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ++ tail) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      (okPart r).map (fun rb => cowList rb.1) =
        some (text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0)) ∧
      rest.val = tail ⦄ := by
  have hpre : (text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0)).length = L.val := by
    simp
  have hl : L.val ≤ buf.length := by
    simp only [Slice.length, h, List.length_append, hpre]; omega
  apply WP.spec_mono (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.parse_rawbytes_spec L buf)
  rintro ⟨r, rest⟩ hr
  simp only [hl, ↓reduceIte, WP.uncurry'_pair] at hr ⊢
  rw [h] at hr
  rw [List.take_left' hpre, List.drop_left' hpre] at hr
  exact hr

end mysql_common
