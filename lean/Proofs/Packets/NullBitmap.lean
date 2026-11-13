import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf

/-! Statements for `struct NullBitmap and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

@[local step]
private theorem vec_as_mut_ok (v : alloc.vec.Vec U8) :
    alloc.vec.Vec.Insts.CoreConvertAsMutSlice.as_mut alloc.alloc.Global v ⦃ s back =>
      s = v.slice ∧ back = fun s => ({ slice := s } : alloc.vec.Vec U8) ⦄ :=
  (WP.spec_ok _).mpr ⟨rfl, rfl⟩

@[local step]
private theorem from_bytes_ok {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8)) (bytes : U) :
    packets.NullBitmap.from_bytes inst asRef bytes ⦃ nb => nb.1 = bytes ⦄ :=
  (WP.spec_ok _).mpr rfl

@[local step]
private theorem bitmap_len_ok {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmap.bitmap_len inst asRef n ⦃ r => r.val = nullBitmapLen off.val n.val ⦄ := by
  unfold packets.NullBitmap.bitmap_len
  simp only [hoff]
  step*
  simp_all [nullBitmapLen]

/-- `ClientSide::BIT_OFFSET` is 0 (from `src/value/mod.rs`; the offset of `COM_STMT_EXECUTE` bitmaps). -/
theorem value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val :
    value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET.val = 0 := by
  unfold value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET; rfl

/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>`: `SIZE` is `None`. -/
theorem packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (inst : value.SerializationSide T) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE inst = none := by
  unfold packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE; rfl

/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>` with context the number of columns: total; the next `bitmap_len` bytes, or an error with the buffer unchanged if there are fewer. -/
theorem packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize inst n buf ⦃ r rest =>
      if nullBitmapLen off.val n.val ≤ buf.length then
        (okPart r).map (fun bm => cowList bm.1) = some (buf.val.take (nullBitmapLen off.val n.val)) ∧
        rest.val = buf.val.drop (nullBitmapLen off.val n.val)
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize
    misc.unexpected_buf_eof misc.io_error_msg
  step*
  · split_ifs at o_post with hl <;> simp_all [okPart]
  · have hl : nullBitmapLen off.val n.val ≤ buf.length := by
      by_contra hc; simp_all
    simp only [bitmap_len_post, hl, ite_true] at o_post
    obtain ⟨h1, h2⟩ := o_post
    simp only [Option.map] at h1
    simp_all [okPart, cowList]

/-- `new`: an all-clear bitmap of `bitmap_len` bytes. -/
theorem packets.NullBitmapTVecU8.new_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmapTVecU8.new inst n ⦃ bm =>
      bm.1.val = List.replicate (nullBitmapLen off.val n.val) (byte 0) ⦄ := by
  unfold packets.NullBitmapTVecU8.new
  step*
  simp_all; right; rfl

/-- `read`: the first `bitmap_len` bytes of `input`, and the rest. -/
theorem packets.NullBitmapTVecU8.read_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : nullBitmapLen off.val n.val ≤ input.length) :
    packets.NullBitmapTVecU8.read inst input n ⦃ bm rest =>
      bm.1.val = input.val.take (nullBitmapLen off.val n.val) ∧
      rest.val = input.val.drop (nullBitmapLen off.val n.val) ⦄ := by
  unfold packets.NullBitmapTVecU8.read
  step*
  refine ⟨?_, by simp_all⟩
  simp_all [alloc.vec.Vec.val, List.slice]

/-- `read` panics (`assert!`) on an input shorter than `bitmap_len`. -/
theorem packets.NullBitmapTVecU8.read_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : input.length < nullBitmapLen off.val n.val) :
    packets.NullBitmapTVecU8.read inst input n = fail .assertionFailure := by
  unfold packets.NullBitmapTVecU8.read
  apply mysql_common.PBUtil.bind_fail_of_spec (bitmap_len_ok inst _ off hoff n hn)
  intro bl hbl
  simp only [massert, Slice.len]
  have hc : ¬ (Usize.ofNatCore input.val.length (by scalar_tac) ≥ bl) := by
    simp only [Slice.length] at hin; scalar_tac
  simp [hc]

@[local step]
private theorem byte_and_bit_ok {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : (i.val + off.val) / 8 < s.length) :
    packets.NullBitmap.byte_and_bit inst asRef self i ⦃ byte bit =>
      byte.val = (i.val + off.val) / 8 ∧ bit.val = 2 ^ ((i.val + off.val) % 8) ⦄ := by
  have e : packets.NullBitmap.byte_and_bit inst asRef self i = (do
      let i0 ← inst.BIT_OFFSET
      let offset ← i + i0
      let byte ← offset / 8#usize
      let i1 ← offset % 8#usize
      let i2 ← lift (UScalar.cast .U8 i1)
      let bit ← 1#u8 <<< i2
      let s ← asRef.as_ref self.1
      massert (byte < Slice.len s)
      ok (byte, bit)) := rfl
  rw [e, hoff]
  step*
  rw [hs, Aeneas.Std.bind_ok]
  step*
  have hk : (i.val + off.val) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hi2 : i2.val = (i.val + off.val) % 8 := by
    rw [i2_post, UScalar.cast_val_eq]; simp_all; omega
  refine ⟨by simp_all, ?_⟩
  rw [bit_post, hi2, Nat.shiftLeft_eq, one_mul]
  apply Nat.mod_eq_of_lt
  have : 2 ^ ((i.val + off.val) % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [U8.size, U8.numBits, UScalarTy.U8_numBits_eq]; omega

private theorem byte_and_bit_fail {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : s.length ≤ (i.val + off.val) / 8) :
    packets.NullBitmap.byte_and_bit inst asRef self i = fail .assertionFailure := by
  have e : packets.NullBitmap.byte_and_bit inst asRef self i = (do
      let i0 ← inst.BIT_OFFSET
      let offset ← i + i0
      let byte ← offset / 8#usize
      let i1 ← offset % 8#usize
      let i2 ← lift (UScalar.cast .U8 i1)
      let bit ← 1#u8 <<< i2
      let s ← asRef.as_ref self.1
      massert (byte < Slice.len s)
      ok (byte, bit)) := rfl
  rw [e, hoff, Aeneas.Std.bind_ok]
  apply mysql_common.PBUtil.bind_fail_of_spec (by step* : (i + off) ⦃ o => o.val = i.val + off.val ⦄)
  intro offset ho
  apply mysql_common.PBUtil.bind_fail_of_spec (by step* : (offset / 8#usize) ⦃ b => b.val = offset.val / 8 ⦄)
  intro byte' hbyte
  apply mysql_common.PBUtil.bind_fail_of_spec (by step* : (offset % 8#usize) ⦃ b => b.val = offset.val % 8 ⦄)
  intro i1 hi1
  apply mysql_common.PBUtil.bind_fail_of_spec ((WP.spec_ok _).mpr rfl :
    lift (UScalar.cast .U8 i1) ⦃ b => b = UScalar.cast .U8 i1 ⦄)
  intro i2 hi2
  have hi2v : i2.val < 8 := by
    rw [hi2, UScalar.cast_val_eq]; have := Nat.mod_lt offset.val (show 8 > 0 by decide)
    simp only [UScalarTy.numBits]; omega
  apply mysql_common.PBUtil.bind_fail_of_spec (by step* : (1#u8 <<< i2) ⦃ _ => True ⦄)
  intro bit _
  rw [hs, Aeneas.Std.bind_ok]
  simp only [massert, Slice.len]
  have : ¬ byte' < Usize.ofNatCore s.val.length (by scalar_tac) := by
    simp only [Slice.length] at hb; scalar_tac
  simp [this]

/-- `bitmap_len`: `(n + 7 + BIT_OFFSET) / 8`. -/
theorem packets.NullBitmap.bitmap_len_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmap.bitmap_len inst asRef n ⦃ r => r.val = nullBitmapLen off.val n.val ⦄ := by
  exact bitmap_len_ok inst asRef off hoff n hn

/-- `from_bytes`: wraps the bytes. -/
theorem packets.NullBitmap.from_bytes_eq {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8)) (bytes : U) :
    packets.NullBitmap.from_bytes inst asRef bytes = ok (bytes, ()) := by
  rfl

/-- `is_null(i)`: bit `i + BIT_OFFSET` of the bytes, for any byte container `U` (given its bytes `s`). -/
theorem packets.NullBitmap.is_null_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : (i.val + off.val) / 8 < s.length) :
    packets.NullBitmap.is_null inst asRef self i ⦃ b => b = bitmapBit off.val s.val i.val ⦄ := by
  have e : packets.NullBitmap.is_null inst asRef self i = (do
      let (byte, bit) ← packets.NullBitmap.byte_and_bit inst asRef self i
      let s ← asRef.as_ref self.1
      let x ← Slice.index_usize s byte
      let i1 ← lift (x &&& bit)
      ok (i1 > 0#u8)) := rfl
  rw [e]
  step with byte_and_bit_ok inst asRef off hoff self s hs i hi hb as ⟨bi, bit, hbyte, hbit⟩
  rw [hs, Aeneas.Std.bind_ok]
  step*
  have hlt : bi.val < s.val.length := by simp at hb; omega
  have hx : s.val.getD ((i.val + off.val) / 8) (byte 0) = x := by
    rw [x_post, ← hbyte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  have hv : i1.val = x.val &&& 2 ^ ((i.val + off.val) % 8) := by
    rw [i1_post, UScalar.val_and, hbit]
  simp only [bitmapBit, bitAt, hx]
  rw [and_two_pow] at hv
  have hgt : (i1 > 0#u8) ↔ 0 < i1.val := by
    rw [gt_iff_lt, UScalar.lt_equiv]; simp
  simp only [hgt]
  split at hv
  · rename_i ht; rw [ht]; simp only [decide_eq_true_eq]; rw [hv]; exact Nat.two_pow_pos _
  · rename_i ht; rw [Bool.not_eq_true] at ht; rw [ht]; simp [hv]

/-- `is_null(i)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
theorem packets.NullBitmap.is_null_panics {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : s.length ≤ (i.val + off.val) / 8) :
    packets.NullBitmap.is_null inst asRef self i = fail .assertionFailure := by
  unfold packets.NullBitmap.is_null
  exact mysql_common.PBUtil.bind_fail_left (byte_and_bit_fail inst asRef off hoff self s hs i hi hb)

/-- `set(i, is_null)` (at `Vec<u8>`): sets bit `i + BIT_OFFSET` to `is_null`, every other bit unchanged. -/
theorem packets.NullBitmap.set_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : (i.val + off.val) / 8 < self.1.length) :
    packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b ⦃ bm =>
      bm.1.length = self.1.length ∧
      ∀ pos, bitAt bm.1.val pos = if pos = i.val + off.val then b else bitAt self.1.val pos ⦄ := by
  have hb' := hb
  obtain ⟨t, pd⟩ := self
  unfold packets.NullBitmap.set
  step with byte_and_bit_ok inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) off hoff (t, pd) (alloc.vec.Vec.deref t) rfl i hi
    (by simpa [alloc.vec.Vec.deref] using hb) as ⟨bi, bit, hbyte, hbit⟩
  have hbi : bi.val < t.slice.length := by
    simp only [alloc.vec.Vec.length, alloc.vec.Vec.val] at hb; simp only [Slice.length]; omega
  have hbt : bi.val < t.val.length := hbi
  generalize hN : i.val + off.val = N at hbyte hbit ⊢
  have hk : N % 8 < 8 := Nat.mod_lt _ (by decide)
  split <;> rename_i hbb
  · step*
    apply (WP.spec_ok ((as_mut_back s1, pd) : packets.NullBitmap T (alloc.vec.Vec U8))).mpr
    subst as_mut_back_post s_post hbb
    have hv : (({slice := s1} : alloc.vec.Vec U8)).val = t.val.set bi.val i1 := by
      simp only [alloc.vec.Vec.val, s1_post, Slice.set_val_eq]
    show (({slice := s1} : alloc.vec.Vec U8)).length = t.length ∧
      ∀ pos, bitAt (({slice := s1} : alloc.vec.Vec U8)).val pos = _
    simp only [alloc.vec.Vec.length, hv, List.length_set, true_and]
    intro pos
    rw [bitAt_set _ _ _ _ hbt]
    simp only [pos_eq_iff pos N, ← hbyte]
    by_cases h1 : pos / 8 = bi.val
    · have hpt : pos / 8 < t.val.length := h1 ▸ hbt
      rw [bitAt_of_lt _ _ hpt, i1_post, UScalar.val_or, hbit, or_two_pow_testBit, i_post]
      by_cases h2 : pos % 8 = N % 8
      · simp [h1, h2]
      · simp only [h1, h2, Ne.symm h2, true_and, ite_true, ite_false, decide_false, Bool.or_false]
        rfl
    · simp [h1]
  · step*
    apply (WP.spec_ok ((as_mut_back s1, pd) : packets.NullBitmap T (alloc.vec.Vec U8))).mpr
    simp only [Bool.not_eq_true] at hbb
    subst as_mut_back_post s_post hbb
    have hv : (({slice := s1} : alloc.vec.Vec U8)).val = t.val.set bi.val i2 := by
      simp only [alloc.vec.Vec.val, s1_post, Slice.set_val_eq]
    show (({slice := s1} : alloc.vec.Vec U8)).length = t.length ∧
      ∀ pos, bitAt (({slice := s1} : alloc.vec.Vec U8)).val pos = _
    simp only [alloc.vec.Vec.length, hv, List.length_set, true_and]
    intro pos
    rw [bitAt_set _ _ _ _ hbt]
    simp only [pos_eq_iff pos N, ← hbyte]
    by_cases h1 : pos / 8 = bi.val
    · have hpt : pos / 8 < t.val.length := h1 ▸ hbt
      have hp8 : pos % 8 < 8 := Nat.mod_lt _ (by decide)
      rw [bitAt_of_lt _ _ hpt, i2_post, UScalar.val_and, Nat.testBit_and, i_post]
      simp only [h1, ite_true, true_and]
      rw [u8_not_testBit _ _ hp8, hbit, Nat.testBit_two_pow]
      subst i1_post
      by_cases h2 : pos % 8 = N % 8
      · simp [h2]
      · simp only [h2, ite_false, Ne.symm h2, decide_false, Bool.not_false, Bool.and_true]
        simp only [alloc.vec.Vec.val]
    · simp [h1]

/-- `set(i, _)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
theorem packets.NullBitmap.set_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : self.1.length ≤ (i.val + off.val) / 8) :
    packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b = fail .assertionFailure := by
  unfold packets.NullBitmap.set
  exact mysql_common.PBUtil.bind_fail_left (byte_and_bit_fail inst _ off hoff self (alloc.vec.Vec.deref self.1) rfl i hi (by simpa [alloc.vec.Vec.deref] using hb))

/-- `AsRef<[u8]> for NullBitmap`: the bytes. -/
theorem packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref_eq {T U : Type} (asRef : core.convert.AsRef U (Slice U8)) (self : packets.NullBitmap T U) :
    packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref asRef self = asRef.as_ref self.1 := by
  rfl

end mysql_common
