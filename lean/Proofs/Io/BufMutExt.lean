import Proofs.Util.IntAndMisc
import Proofs.Util.ParseBuf

/-! Statements for `trait BufMutExt (at Vec<u8>)` (spec file: `Specs/Io.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `put_lenenc_int`: appends the length-encoded integer `x` (protocol table in
    `Defs/LenEnc.lean`). Precondition: the buffer can grow by the encoding's length (Aeneas lets a `Vec` grow
    to `usize::MAX` and models allocation as infallible; real Rust aborts on OOM). -/
theorem io.BufMutExt.put_lenenc_int_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + (lenencInt x.val).length ≤ Usize.max) :
    io.BufMutExt.put_lenenc_int.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄ := by
  unfold io.BufMutExt.put_lenenc_int.default

  simp only [lenencInt] at h ⊢
  by_cases h1 : x.val < 251
  · have c1 : x < 251#u64 := by scalar_tac
    simp only [c1, h1, ↓reduceIte, List.length_singleton] at h ⊢
    step*
    rw [buf'_post]
    have : i = byte x.val := by
      apply UScalar.eq_of_val_eq; rw [i_post, UScalar.cast_val_eq, PBUtil.byte_val]; rfl
    rw [this]
  · have c1 : ¬ x < 251#u64 := by scalar_tac
    simp only [c1, h1, ↓reduceIte] at h ⊢
    by_cases h2 : x.val < 2 ^ 16
    · have c2 : x < 65536#u64 := by scalar_tac
      simp only [c2, h2, ↓reduceIte, List.length_cons, IntAndMisc.length_leBytes'] at h ⊢
      step*
      · have : self1.val.length = buf.val.length + 1 := by simp [self1_post]
        scalar_tac
      · rw [buf'_post, self1_post]; simp; rfl
    · have c2 : ¬ x < 65536#u64 := by scalar_tac
      simp only [c2, h2, ↓reduceIte] at h ⊢
      by_cases h3 : x.val < 2 ^ 24
      · have c3 : x < 16777216#u64 := by scalar_tac
        simp only [c3, h3, ↓reduceIte, List.length_cons, IntAndMisc.length_leBytes'] at h ⊢
        step*
        · have : self1.val.length = buf.val.length + 1 := by simp [self1_post]
          scalar_tac
        · rw [buf'_post, self1_post]; simp; rfl
      · have c3 : ¬ x < 16777216#u64 := by scalar_tac
        simp only [c3, h3, ↓reduceIte, List.length_cons, IntAndMisc.length_leBytes'] at h ⊢
        step*
        · have : self1.val.length = buf.val.length + 1 := by simp [self1_post]
          scalar_tac
        · rw [buf'_post, self1_post]; simp; rfl

/-- `put_lenenc_str`: appends the length-encoded string `x` (its length as a length-encoded
    integer, then its bytes). -/
theorem io.BufMutExt.put_lenenc_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + (lenencStr x.val).length ≤ Usize.max) :
    io.BufMutExt.put_lenenc_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencStr x.val ⦄ := by
  unfold io.BufMutExt.put_lenenc_str.default
  show Std.bind (lift (UScalar.cast .U64 x.len)) (fun i1 => Std.bind (io.BufMutExt.put_lenenc_int.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf i1) (fun self1 => alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice self1 x)) ⦃ buf' => buf'.val = buf.val ++ lenencStr x.val ⦄
  simp only [lenencStr, List.length_append] at h ⊢
  have hx : x.val.length < 2 ^ 64 := by
    have : x.val.length ≤ Usize.max := by scalar_tac
    have : Usize.max < 2 ^ 64 := by
      simp only [Usize.max, Usize.numBits]; cases System.Platform.numBits_eq <;> simp [*]
    omega
  have hi1 : (UScalar.cast UScalarTy.U64 x.len).val = x.val.length := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simpa using hx)
  rw [show lift (UScalar.cast .U64 x.len) = ok (UScalar.cast .U64 x.len) from rfl, Std.bind_ok]
  refine spec_bind (io.BufMutExt.put_lenenc_int_spec buf _ (by rw [hi1]; omega)) ?_
  intro b1 hb1
  rw [hi1] at hb1
  apply spec_mono (IntAndMisc.put_slice_spec b1 x (by simp [hb1] at *; scalar_tac))
  intro b hb
  rw [hb, hb1]; simp

/-- `put_u24_le`: appends the low 3 bytes of `x`, little-endian (the top byte of `x` is dropped). -/
theorem io.BufMutExt.put_u24_le_spec (buf : alloc.vec.Vec U8) (x : U32)
    (h : buf.length + 3 ≤ Usize.max) :
    io.BufMutExt.put_u24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄ := by
  unfold io.BufMutExt.put_u24_le.default
  step*

/-- `put_i24_le`: appends the low 3 bytes of the two's complement of `x`, little-endian (no range check: `x` is taken mod `2^24`). -/
theorem io.BufMutExt.put_i24_le_spec (buf : alloc.vec.Vec U8) (x : I32)
    (h : buf.length + 3 ≤ Usize.max) :
    io.BufMutExt.put_i24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 3 x.val ⦄ := by
  unfold io.BufMutExt.put_i24_le.default
  step*

/-- `put_u48_le`: appends the low 6 bytes of `x`, little-endian. -/
theorem io.BufMutExt.put_u48_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 6 ≤ Usize.max) :
    io.BufMutExt.put_u48_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 6 x.val ⦄ := by
  unfold io.BufMutExt.put_u48_le.default
  step*

/-- `put_u56_le`: appends the low 7 bytes of `x`, little-endian. -/
theorem io.BufMutExt.put_u56_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 7 ≤ Usize.max) :
    io.BufMutExt.put_u56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 7 x.val ⦄ := by
  unfold io.BufMutExt.put_u56_le.default
  step*

/-- `put_i56_le`: appends the low 7 bytes of the two's complement of `x`, little-endian. -/
theorem io.BufMutExt.put_i56_le_spec (buf : alloc.vec.Vec U8) (x : I64)
    (h : buf.length + 7 ≤ Usize.max) :
    io.BufMutExt.put_i56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 7 x.val ⦄ := by
  unfold io.BufMutExt.put_i56_le.default
  step*

/-- `put_u8_str`: appends a `u8` length and the bytes; a string longer than 255 bytes is
    silently truncated to its first 255 bytes (documented). -/
theorem io.BufMutExt.put_u8_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 1 + min x.length 255 ≤ Usize.max) :
    io.BufMutExt.put_u8_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ byte (min x.length 255) :: x.val.take 255 ⦄ := by
  unfold io.BufMutExt.put_u8_str.default
  step*
  all_goals
    have hi1 : i1.val = 255 := by rw [i1_post, IntAndMisc.cast_usize_small _ (by decide)]; rfl
    have hlen : len.val = min x.length 255 := by rw [len_post, hi1]; rfl
  · have : self1.val.length = buf.val.length + 1 := by simp [self1_post]
    scalar_tac
  · have hi2 : i2 = byte (min x.length 255) := by
      apply UScalar.eq_of_val_eq; rw [i2_post, UScalar.cast_val_eq, PBUtil.byte_val, hlen]; rfl
    rw [buf'_post, self1_post, s1_post, hi2, hlen]
    simp [List.slice]
    simp only [Slice.length] at *
    omega

/-- `put_u32_str`: appends a little-endian `u32` length and the bytes; a string longer than
    `u32::MAX` bytes is silently truncated (documented). -/
theorem io.BufMutExt.put_u32_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 4 + min x.length (2 ^ 32 - 1) ≤ Usize.max) :
    io.BufMutExt.put_u32_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min x.length (2 ^ 32 - 1)) ++ x.val.take (2 ^ 32 - 1) ⦄ := by
  unfold io.BufMutExt.put_u32_str.default
  step*
  all_goals
    have hi1 : i1.val = 2 ^ 32 - 1 := by rw [i1_post, IntAndMisc.cast_usize_small _ (by decide)]; rfl
    have hlen : len.val = min x.length (2 ^ 32 - 1) := by rw [len_post, hi1]; rfl
  · have : self1.val.length = buf.val.length + 4 := by simp [self1_post]
    scalar_tac
  · have hi2 : i2.val = min x.length (2 ^ 32 - 1) := by
      rw [i2_post, UScalar.cast_val_eq, hlen]; apply Nat.mod_eq_of_lt; simp only [UScalarTy.numBits]; omega
    rw [buf'_post, self1_post, s1_post, hi2, hlen]
    simp [List.slice]
    simp only [Slice.length] at *
    omega

end mysql_common
