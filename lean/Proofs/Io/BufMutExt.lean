import Defs

/-! Statements for `trait BufMutExt (at Vec<u8>)` (spec file: `Specs/Io.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `put_lenenc_int`: appends the length-encoded integer `x` (protocol table in
    `Defs/LenEnc.lean`). Precondition: the buffer can grow by 9 bytes (Aeneas lets a `Vec` grow
    to `usize::MAX` and models allocation as infallible; real Rust aborts on OOM). -/
theorem io.BufMutExt.put_lenenc_int_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_lenenc_int.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄ := by
  sorry

/-- `put_lenenc_str`: appends the length-encoded string `x` (its length as a length-encoded
    integer, then its bytes). -/
theorem io.BufMutExt.put_lenenc_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 9 + x.length ≤ Usize.max) :
    io.BufMutExt.put_lenenc_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencStr x.val ⦄ := by
  sorry

/-- `put_u24_le`: appends the low 3 bytes of `x`, little-endian (the top byte of `x` is dropped). -/
theorem io.BufMutExt.put_u24_le_spec (buf : alloc.vec.Vec U8) (x : U32)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_u24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄ := by
  sorry

/-- `put_i24_le`: appends the low 3 bytes of the two's complement of `x`, little-endian (no range check: `x` is taken mod `2^24`). -/
theorem io.BufMutExt.put_i24_le_spec (buf : alloc.vec.Vec U8) (x : I32)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_i24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 3 x.val ⦄ := by
  sorry

/-- `put_u48_le`: appends the low 6 bytes of `x`, little-endian. -/
theorem io.BufMutExt.put_u48_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_u48_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 6 x.val ⦄ := by
  sorry

/-- `put_u56_le`: appends the low 7 bytes of `x`, little-endian. -/
theorem io.BufMutExt.put_u56_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_u56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 7 x.val ⦄ := by
  sorry

/-- `put_i56_le`: appends the low 7 bytes of the two's complement of `x`, little-endian. -/
theorem io.BufMutExt.put_i56_le_spec (buf : alloc.vec.Vec U8) (x : I64)
    (h : buf.length + 9 ≤ Usize.max) :
    io.BufMutExt.put_i56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 7 x.val ⦄ := by
  sorry

/-- `put_u8_str`: appends a `u8` length and the bytes; a string longer than 255 bytes is
    silently truncated to its first 255 bytes (documented). -/
theorem io.BufMutExt.put_u8_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 1 + x.length ≤ Usize.max) :
    io.BufMutExt.put_u8_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ byte (min x.length 255) :: x.val.take 255 ⦄ := by
  sorry

/-- `put_u32_str`: appends a little-endian `u32` length and the bytes; a string longer than
    `u32::MAX` bytes is silently truncated (documented). -/
theorem io.BufMutExt.put_u32_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 4 + x.length ≤ Usize.max) :
    io.BufMutExt.put_u32_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min x.length (2 ^ 32 - 1)) ++ x.val.take (2 ^ 32 - 1) ⦄ := by
  sorry

end mysql_common
