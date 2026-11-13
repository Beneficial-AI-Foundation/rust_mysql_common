import Proofs.Io.BufMutExt
import Proofs.Io.ParseBuf

/-!
# `src/io.rs`
    Specs of the byte-buffer primitives: the reader `ParseBuf` and the writer extension `BufMutExt`.

    **Configuration.** As translated by `scripts/aeneas-translate.sh`: target
    `x86_64-unknown-linux-gnu`, features `derive,flate2/rust_backend,chrono,time,rust_decimal,bigdecimal,frunk`
    (no default features). Statements that depend on `usize` being 64-bit take `Target64`.

    **Reading the statements.** `f x ⦃ r => P r ⦄` means `f x` returns without panicking and its
    result satisfies `P`. `&mut self` methods return the updated value as part of the result: for
    `ParseBuf` methods the last component (`rest`) is the buffer afterwards; for `BufMutExt` the result
    is the vector afterwards. Unchecked readers are stated under the length precondition that rules
    out their panic; every `checked_*` reader is stated for every input. A `Vec` is assumed able to grow
    (Aeneas models allocation as infallible, bounded only by `usize::MAX`).
    Panics are stated as equations `f x = fail e`: `f x` stops with a Rust panic (it neither returns nor runs forever). `e` is the Aeneas library's label for the kind of panic (`.panic` in general, `.assertionFailure` for a failed `assert!`, `.undef` for an out-of-range `[n..]`); Rust does not distinguish them.

    **Definitions used.** `Defs/Bytes.lean` (`leBytes`, `leBytesI`, `leNat`, `beNat`, `toSigned`,
    `byte`, `beforeZero`, `okPart`, `Target64`), `Defs/LenEnc.lean` (`lenencInt`, `lenencStr`,
    `checkedLenencInt`, `checkedLenencStr`, `checkedLenPrefixed`).

    **Not covered.** `impl io::Read for ParseBuf`, `ReadMysqlExt`, `WriteMysqlExt` (I/O traits, not
    translated). `BufMutExt` is stated at `Vec<u8>`, its only use in the crate (translation patch 01
    replaces `bytes::BufMut` by a crate-local trait implemented for `Vec<u8>`). `parse`/`parse_unchecked`
    are stated generically; their instances are in `Specs/Misc/Raw/*`.

    **Behaviour to note.** The odd-width signed readers (`eat_i24_*`, `eat_i40_*`, `eat_i48_*`,
    `eat_i56_*`) zero-extend; `checked_eat_lenenc_int` decodes `0xFB`/`0xFF` as `0`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `trait BufMutExt (at Vec<u8>)` -/

/-- `put_lenenc_int`: appends the length-encoded integer `x` (protocol table in
    `Defs/LenEnc.lean`). Precondition: the buffer can grow by the encoding's length (Aeneas lets a `Vec` grow
    to `usize::MAX` and models allocation as infallible; real Rust aborts on OOM). -/
recall io.BufMutExt.put_lenenc_int_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + (lenencInt x.val).length ≤ Usize.max) :
    io.BufMutExt.put_lenenc_int.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_lenenc_int_spec
/-- `put_lenenc_str`: appends the length-encoded string `x` (its length as a length-encoded
    integer, then its bytes). -/
recall io.BufMutExt.put_lenenc_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + (lenencStr x.val).length ≤ Usize.max) :
    io.BufMutExt.put_lenenc_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ lenencStr x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_lenenc_str_spec
/-- `put_u24_le`: appends the low 3 bytes of `x`, little-endian (the top byte of `x` is dropped). -/
recall io.BufMutExt.put_u24_le_spec (buf : alloc.vec.Vec U8) (x : U32)
    (h : buf.length + 3 ≤ Usize.max) :
    io.BufMutExt.put_u24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_u24_le_spec
/-- `put_i24_le`: appends the low 3 bytes of the two's complement of `x`, little-endian (no range check: `x` is taken mod `2^24`). -/
recall io.BufMutExt.put_i24_le_spec (buf : alloc.vec.Vec U8) (x : I32)
    (h : buf.length + 3 ≤ Usize.max) :
    io.BufMutExt.put_i24_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 3 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_i24_le_spec
/-- `put_u48_le`: appends the low 6 bytes of `x`, little-endian. -/
recall io.BufMutExt.put_u48_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 6 ≤ Usize.max) :
    io.BufMutExt.put_u48_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 6 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_u48_le_spec
/-- `put_u56_le`: appends the low 7 bytes of `x`, little-endian. -/
recall io.BufMutExt.put_u56_le_spec (buf : alloc.vec.Vec U8) (x : U64)
    (h : buf.length + 7 ≤ Usize.max) :
    io.BufMutExt.put_u56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 7 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_u56_le_spec
/-- `put_i56_le`: appends the low 7 bytes of the two's complement of `x`, little-endian. -/
recall io.BufMutExt.put_i56_le_spec (buf : alloc.vec.Vec U8) (x : I64)
    (h : buf.length + 7 ≤ Usize.max) :
    io.BufMutExt.put_i56_le.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytesI 7 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_i56_le_spec
/-- `put_u8_str`: appends a `u8` length and the bytes; a string longer than 255 bytes is
    silently truncated to its first 255 bytes (documented). -/
recall io.BufMutExt.put_u8_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 1 + min x.length 255 ≤ Usize.max) :
    io.BufMutExt.put_u8_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ byte (min x.length 255) :: x.val.take 255 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_u8_str_spec
/-- `put_u32_str`: appends a little-endian `u32` length and the bytes; a string longer than
    `u32::MAX` bytes is silently truncated (documented). -/
recall io.BufMutExt.put_u32_str_spec (buf : alloc.vec.Vec U8) (x : Slice U8)
    (h : buf.length + 4 + min x.length (2 ^ 32 - 1) ≤ Usize.max) :
    io.BufMutExt.put_u32_str.default (io.BufMutExt.Blanket alloc.vec.VecU8.Insts.Mysql_commonIoBufMut) buf x
      ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min x.length (2 ^ 32 - 1)) ++ x.val.take (2 ^ 32 - 1) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.BufMutExt.put_u32_str_spec
/-! ### `impl ParseBuf` -/

/-- `parse_unchecked::<T>(ctx)` is `T::deserialize(ctx, self)` (generic in `T`; for the
    instances that matter see `Specs/Misc/Raw/*`). Its doc warns that it "may panic if `T::SIZE`
    is some": the fixed-size deserializers (`RawInt<LeU16>`, `[u8; N]`, ...) do not check the
    length, see their specs. -/
recall io.ParseBuf.parse_unchecked_eq {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) :
    io.ParseBuf.parse_unchecked inst buf ctx = inst.deserialize ctx buf

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.parse_unchecked_eq
/-- `parse` of a type without a fixed size (`T::SIZE = None`) is `T::deserialize`. -/
recall io.ParseBuf.parse_of_size_none {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx)
    (hs : inst.SIZE = ok none) :
    io.ParseBuf.parse inst buf ctx = inst.deserialize ctx buf

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.parse_of_size_none
/-- `parse` of a type of fixed size `n` (`T::SIZE = Some(n)`) on a buffer shorter than `n`:
    an error, and the buffer is unchanged (whatever `T::deserialize` does). -/
recall io.ParseBuf.parse_of_size_short {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : buf.length < n.val) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.parse_of_size_short
/-- `parse` of a type of fixed size `n` on a buffer of at least `n` bytes: `T::deserialize` runs on
    the first `n` bytes (so it cannot panic for lack of input), and exactly `n` bytes are consumed
    whatever it consumes of them (bytes it leaves unread are skipped). Stated for any property
    `P` of the result that `T::deserialize` guarantees on that `n`-byte buffer. -/
recall io.ParseBuf.parse_of_size {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : n.val ≤ buf.length) (P : Option T → Prop)
    (hd : ∀ sub : io.ParseBuf, sub.val = buf.val.take n.val →
      inst.deserialize ctx sub ⦃ r _ => P (okPart r) ⦄) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => P (okPart r) ∧ rest.val = buf.val.drop n.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.parse_of_size
/-- `is_empty`: whether the buffer is empty. -/
recall io.ParseBuf.is_empty_spec (buf : io.ParseBuf) :
    io.ParseBuf.is_empty buf ⦃ b => (b ↔ buf.val = []) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.is_empty_spec
/-- `len`: the number of bytes in the buffer. -/
recall io.ParseBuf.len_spec (buf : io.ParseBuf) :
    io.ParseBuf.len buf ⦃ n => n.val = buf.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.len_spec
/-- `skip(cnt)`: drops the first `cnt` bytes. Panics if `cnt > len` (`skip_panics`). -/
recall io.ParseBuf.skip_spec (buf : io.ParseBuf) (cnt : Usize) (h : cnt.val ≤ buf.length) :
    io.ParseBuf.skip buf cnt ⦃ rest => rest.val = buf.val.drop cnt.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.skip_spec
/-- `skip(cnt)` panics if `cnt > len` (`.undef` is the Aeneas library's label for the out-of-range `[cnt..]`). -/
recall io.ParseBuf.skip_panics (buf : io.ParseBuf) (cnt : Usize) (h : buf.length < cnt.val) :
    io.ParseBuf.skip buf cnt = fail .undef

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.skip_panics
/-- `checked_skip(cnt)`: total; `true` and drops `cnt` bytes if there are that many, else `false` and the buffer is unchanged. -/
recall io.ParseBuf.checked_skip_spec (buf : io.ParseBuf) (cnt : Usize) :
    io.ParseBuf.checked_skip buf cnt ⦃ b rest =>
      if cnt.val ≤ buf.length then b = true ∧ rest.val = buf.val.drop cnt.val
      else b = false ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_skip_spec
/-- `eat(n)`: splits off the first `n` bytes. Panics if `n > len` (documented; `eat_panics`). -/
recall io.ParseBuf.eat_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_spec
/-- `eat(n)` panics if `n > len` (documented). -/
recall io.ParseBuf.eat_panics (buf : io.ParseBuf) (n : Usize) (h : buf.length < n.val) :
    io.ParseBuf.eat buf n = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_panics
/-- `eat_buf(n)`: as `eat`, returning a `ParseBuf`. -/
recall io.ParseBuf.eat_buf_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat_buf buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_buf_spec
/-- `eat_buf(n)` panics if `n > len`. -/
recall io.ParseBuf.eat_buf_panics (buf : io.ParseBuf) (n : Usize) (h : buf.length < n.val) :
    io.ParseBuf.eat_buf buf n = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_buf_panics
/-- `checked_eat(n)`: total; `eat(n)` if there are `n` bytes, else `None` and the buffer is unchanged. -/
recall io.ParseBuf.checked_eat_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_spec
/-- `checked_eat_buf(n)`: as `checked_eat`, returning a `ParseBuf`. -/
recall io.ParseBuf.checked_eat_buf_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat_buf buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_buf_spec
/-- `eat_all`: total; returns the whole buffer and leaves it empty. -/
recall io.ParseBuf.eat_all_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_all buf ⦃ s rest => s.val = buf.val ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_all_spec
/-- `eat_u8`: consumes 1 byte from the head of the buffer and returns the 1-byte little-endian unsigned integer. Panics on fewer (`eat_u8_panics`). -/
recall io.ParseBuf.eat_u8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_u8 buf ⦃ x rest =>
      x.val = leNat (buf.val.take 1) ∧ rest.val = buf.val.drop 1 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u8_spec
/-- `eat_u8` panics on a buffer of fewer than 1 byte. -/
recall io.ParseBuf.eat_u8_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    io.ParseBuf.eat_u8 buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u8_panics
/-- `checked_eat_u8`: total; with at least 1 byte, the 1-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u8_spec
/-- `eat_i8`: consumes 1 byte from the head of the buffer and returns the 1-byte little-endian two's-complement integer. Panics on fewer (`eat_i8_panics`). -/
recall io.ParseBuf.eat_i8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_i8 buf ⦃ x rest =>
      x.val = toSigned 8 (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i8_spec
/-- `eat_i8` panics on a buffer of fewer than 1 byte. -/
recall io.ParseBuf.eat_i8_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    io.ParseBuf.eat_i8 buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i8_panics
/-- `checked_eat_i8`: total; with at least 1 byte, the 1-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i8_spec
/-- `eat_u16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian unsigned integer. Panics on fewer (`eat_u16_le_panics`). -/
recall io.ParseBuf.eat_u16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u16_le_spec
/-- `eat_u16_le` panics on a buffer of fewer than 2 bytes. -/
recall io.ParseBuf.eat_u16_le_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    io.ParseBuf.eat_u16_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u16_le_panics
/-- `checked_eat_u16_le`: total; with at least 2 bytes, the 2-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u16_le_spec
/-- `eat_i16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian two's-complement integer. Panics on fewer (`eat_i16_le_panics`). -/
recall io.ParseBuf.eat_i16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_le buf ⦃ x rest =>
      x.val = toSigned 16 (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i16_le_spec
/-- `eat_i16_le` panics on a buffer of fewer than 2 bytes. -/
recall io.ParseBuf.eat_i16_le_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    io.ParseBuf.eat_i16_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i16_le_panics
/-- `checked_eat_i16_le`: total; with at least 2 bytes, the 2-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i16_le_spec
/-- `eat_u16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian unsigned integer. Panics on fewer (`eat_u16_be_panics`). -/
recall io.ParseBuf.eat_u16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u16_be_spec
/-- `eat_u16_be` panics on a buffer of fewer than 2 bytes. -/
recall io.ParseBuf.eat_u16_be_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    io.ParseBuf.eat_u16_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u16_be_panics
/-- `checked_eat_u16_be`: total; with at least 2 bytes, the 2-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u16_be_spec
/-- `eat_i16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian two's-complement integer. Panics on fewer (`eat_i16_be_panics`). -/
recall io.ParseBuf.eat_i16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_be buf ⦃ x rest =>
      x.val = toSigned 16 (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i16_be_spec
/-- `eat_i16_be` panics on a buffer of fewer than 2 bytes. -/
recall io.ParseBuf.eat_i16_be_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    io.ParseBuf.eat_i16_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i16_be_panics
/-- `checked_eat_i16_be`: total; with at least 2 bytes, the 2-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (beNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i16_be_spec
/-- `eat_u24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian unsigned integer. Panics on fewer (`eat_u24_le_panics`). -/
recall io.ParseBuf.eat_u24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u24_le_spec
/-- `eat_u24_le` panics on a buffer of fewer than 3 bytes. -/
recall io.ParseBuf.eat_u24_le_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    io.ParseBuf.eat_u24_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u24_le_panics
/-- `checked_eat_u24_le`: total; with at least 3 bytes, the 3-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u24_le_spec
/-- `eat_i24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian integer, zero-extended. Panics on fewer (`eat_i24_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
recall io.ParseBuf.eat_i24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i24_le_spec
/-- `eat_i24_le` panics on a buffer of fewer than 3 bytes. -/
recall io.ParseBuf.eat_i24_le_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    io.ParseBuf.eat_i24_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i24_le_panics
/-- `checked_eat_i24_le`: total; with at least 3 bytes, the 3-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
recall io.ParseBuf.checked_eat_i24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i24_le_spec
/-- `eat_u24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian unsigned integer. Panics on fewer (`eat_u24_be_panics`). -/
recall io.ParseBuf.eat_u24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u24_be_spec
/-- `eat_u24_be` panics on a buffer of fewer than 3 bytes. -/
recall io.ParseBuf.eat_u24_be_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    io.ParseBuf.eat_u24_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u24_be_panics
/-- `checked_eat_u24_be`: total; with at least 3 bytes, the 3-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u24_be_spec
/-- `eat_i24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian integer, zero-extended. Panics on fewer (`eat_i24_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i24_be_spec
/-- `eat_i24_be` panics on a buffer of fewer than 3 bytes. -/
recall io.ParseBuf.eat_i24_be_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    io.ParseBuf.eat_i24_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i24_be_panics
/-- `checked_eat_i24_be`: total; with at least 3 bytes, the 3-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i24_be_spec
/-- `eat_u32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian unsigned integer. Panics on fewer (`eat_u32_le_panics`). -/
recall io.ParseBuf.eat_u32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_le_spec
/-- `eat_u32_le` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_u32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_u32_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_le_panics
/-- `checked_eat_u32_le`: total; with at least 4 bytes, the 4-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u32_le_spec
/-- `eat_i32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian two's-complement integer. Panics on fewer (`eat_i32_le_panics`). -/
recall io.ParseBuf.eat_i32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_le buf ⦃ x rest =>
      x.val = toSigned 32 (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i32_le_spec
/-- `eat_i32_le` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_i32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_i32_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i32_le_panics
/-- `checked_eat_i32_le`: total; with at least 4 bytes, the 4-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i32_le_spec
/-- `eat_u32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian unsigned integer. Panics on fewer (`eat_u32_be_panics`). -/
recall io.ParseBuf.eat_u32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_be_spec
/-- `eat_u32_be` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_u32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_u32_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_be_panics
/-- `checked_eat_u32_be`: total; with at least 4 bytes, the 4-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u32_be_spec
/-- `eat_i32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian two's-complement integer. Panics on fewer (`eat_i32_be_panics`). -/
recall io.ParseBuf.eat_i32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_be buf ⦃ x rest =>
      x.val = toSigned 32 (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i32_be_spec
/-- `eat_i32_be` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_i32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_i32_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i32_be_panics
/-- `checked_eat_i32_be`: total; with at least 4 bytes, the 4-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (beNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i32_be_spec
/-- `eat_u40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian unsigned integer. Panics on fewer (`eat_u40_le_panics`). -/
recall io.ParseBuf.eat_u40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u40_le_spec
/-- `eat_u40_le` panics on a buffer of fewer than 5 bytes. -/
recall io.ParseBuf.eat_u40_le_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    io.ParseBuf.eat_u40_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u40_le_panics
/-- `checked_eat_u40_le`: total; with at least 5 bytes, the 5-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u40_le_spec
/-- `eat_i40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian integer, zero-extended. Panics on fewer (`eat_i40_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i40_le_spec
/-- `eat_i40_le` panics on a buffer of fewer than 5 bytes. -/
recall io.ParseBuf.eat_i40_le_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    io.ParseBuf.eat_i40_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i40_le_panics
/-- `checked_eat_i40_le`: total; with at least 5 bytes, the 5-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i40_le_spec
/-- `eat_u40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian unsigned integer. Panics on fewer (`eat_u40_be_panics`). -/
recall io.ParseBuf.eat_u40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u40_be_spec
/-- `eat_u40_be` panics on a buffer of fewer than 5 bytes. -/
recall io.ParseBuf.eat_u40_be_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    io.ParseBuf.eat_u40_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u40_be_panics
/-- `checked_eat_u40_be`: total; with at least 5 bytes, the 5-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u40_be_spec
/-- `eat_i40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian integer, zero-extended. Panics on fewer (`eat_i40_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i40_be_spec
/-- `eat_i40_be` panics on a buffer of fewer than 5 bytes. -/
recall io.ParseBuf.eat_i40_be_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    io.ParseBuf.eat_i40_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i40_be_panics
/-- `checked_eat_i40_be`: total; with at least 5 bytes, the 5-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i40_be_spec
/-- `eat_u48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian unsigned integer. Panics on fewer (`eat_u48_le_panics`). -/
recall io.ParseBuf.eat_u48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u48_le_spec
/-- `eat_u48_le` panics on a buffer of fewer than 6 bytes. -/
recall io.ParseBuf.eat_u48_le_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    io.ParseBuf.eat_u48_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u48_le_panics
/-- `checked_eat_u48_le`: total; with at least 6 bytes, the 6-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u48_le_spec
/-- `eat_i48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian integer, zero-extended. Panics on fewer (`eat_i48_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i48_le_spec
/-- `eat_i48_le` panics on a buffer of fewer than 6 bytes. -/
recall io.ParseBuf.eat_i48_le_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    io.ParseBuf.eat_i48_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i48_le_panics
/-- `checked_eat_i48_le`: total; with at least 6 bytes, the 6-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i48_le_spec
/-- `eat_u48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian unsigned integer. Panics on fewer (`eat_u48_be_panics`). -/
recall io.ParseBuf.eat_u48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u48_be_spec
/-- `eat_u48_be` panics on a buffer of fewer than 6 bytes. -/
recall io.ParseBuf.eat_u48_be_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    io.ParseBuf.eat_u48_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u48_be_panics
/-- `checked_eat_u48_be`: total; with at least 6 bytes, the 6-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u48_be_spec
/-- `eat_i48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian integer, zero-extended. Panics on fewer (`eat_i48_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i48_be_spec
/-- `eat_i48_be` panics on a buffer of fewer than 6 bytes. -/
recall io.ParseBuf.eat_i48_be_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    io.ParseBuf.eat_i48_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i48_be_panics
/-- `checked_eat_i48_be`: total; with at least 6 bytes, the 6-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i48_be_spec
/-- `eat_u56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian unsigned integer. Panics on fewer (`eat_u56_le_panics`). -/
recall io.ParseBuf.eat_u56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u56_le_spec
/-- `eat_u56_le` panics on a buffer of fewer than 7 bytes. -/
recall io.ParseBuf.eat_u56_le_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    io.ParseBuf.eat_u56_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u56_le_panics
/-- `checked_eat_u56_le`: total; with at least 7 bytes, the 7-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u56_le_spec
/-- `eat_i56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian integer, zero-extended. Panics on fewer (`eat_i56_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
recall io.ParseBuf.eat_i56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i56_le_spec
/-- `eat_i56_le` panics on a buffer of fewer than 7 bytes. -/
recall io.ParseBuf.eat_i56_le_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    io.ParseBuf.eat_i56_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i56_le_panics
/-- `checked_eat_i56_le`: total; with at least 7 bytes, the 7-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
recall io.ParseBuf.checked_eat_i56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i56_le_spec
/-- `eat_u56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian unsigned integer. Panics on fewer (`eat_u56_be_panics`). -/
recall io.ParseBuf.eat_u56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u56_be_spec
/-- `eat_u56_be` panics on a buffer of fewer than 7 bytes. -/
recall io.ParseBuf.eat_u56_be_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    io.ParseBuf.eat_u56_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u56_be_panics
/-- `checked_eat_u56_be`: total; with at least 7 bytes, the 7-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u56_be_spec
/-- `eat_i56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian integer, zero-extended. Panics on fewer (`eat_i56_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. -/
recall io.ParseBuf.eat_i56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i56_be_spec
/-- `eat_i56_be` panics on a buffer of fewer than 7 bytes. -/
recall io.ParseBuf.eat_i56_be_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    io.ParseBuf.eat_i56_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i56_be_panics
/-- `checked_eat_i56_be`: total; with at least 7 bytes, the 7-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. -/
recall io.ParseBuf.checked_eat_i56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i56_be_spec
/-- `eat_u64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian unsigned integer. Panics on fewer (`eat_u64_le_panics`). -/
recall io.ParseBuf.eat_u64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u64_le_spec
/-- `eat_u64_le` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_u64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_u64_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u64_le_panics
/-- `checked_eat_u64_le`: total; with at least 8 bytes, the 8-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u64_le_spec
/-- `eat_i64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian two's-complement integer. Panics on fewer (`eat_i64_le_panics`). -/
recall io.ParseBuf.eat_i64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_le buf ⦃ x rest =>
      x.val = toSigned 64 (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i64_le_spec
/-- `eat_i64_le` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_i64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_i64_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i64_le_panics
/-- `checked_eat_i64_le`: total; with at least 8 bytes, the 8-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i64_le_spec
/-- `eat_u64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian unsigned integer. Panics on fewer (`eat_u64_be_panics`). -/
recall io.ParseBuf.eat_u64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u64_be_spec
/-- `eat_u64_be` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_u64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_u64_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u64_be_panics
/-- `checked_eat_u64_be`: total; with at least 8 bytes, the 8-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u64_be_spec
/-- `eat_i64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian two's-complement integer. Panics on fewer (`eat_i64_be_panics`). -/
recall io.ParseBuf.eat_i64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_be buf ⦃ x rest =>
      x.val = toSigned 64 (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i64_be_spec
/-- `eat_i64_be` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_i64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_i64_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i64_be_panics
/-- `checked_eat_i64_be`: total; with at least 8 bytes, the 8-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (beNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i64_be_spec
/-- `eat_u128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian unsigned integer. Panics on fewer (`eat_u128_le_panics`). -/
recall io.ParseBuf.eat_u128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u128_le_spec
/-- `eat_u128_le` panics on a buffer of fewer than 16 bytes. -/
recall io.ParseBuf.eat_u128_le_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    io.ParseBuf.eat_u128_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u128_le_panics
/-- `checked_eat_u128_le`: total; with at least 16 bytes, the 16-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u128_le_spec
/-- `eat_i128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian two's-complement integer. Panics on fewer (`eat_i128_le_panics`). -/
recall io.ParseBuf.eat_i128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_le buf ⦃ x rest =>
      x.val = toSigned 128 (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i128_le_spec
/-- `eat_i128_le` panics on a buffer of fewer than 16 bytes. -/
recall io.ParseBuf.eat_i128_le_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    io.ParseBuf.eat_i128_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i128_le_panics
/-- `checked_eat_i128_le`: total; with at least 16 bytes, the 16-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (leNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i128_le_spec
/-- `eat_u128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian unsigned integer. Panics on fewer (`eat_u128_be_panics`). -/
recall io.ParseBuf.eat_u128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u128_be_spec
/-- `eat_u128_be` panics on a buffer of fewer than 16 bytes. -/
recall io.ParseBuf.eat_u128_be_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    io.ParseBuf.eat_u128_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u128_be_panics
/-- `checked_eat_u128_be`: total; with at least 16 bytes, the 16-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_u128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u128_be_spec
/-- `eat_i128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian two's-complement integer. Panics on fewer (`eat_i128_be_panics`). -/
recall io.ParseBuf.eat_i128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_be buf ⦃ x rest =>
      x.val = toSigned 128 (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i128_be_spec
/-- `eat_i128_be` panics on a buffer of fewer than 16 bytes. -/
recall io.ParseBuf.eat_i128_be_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    io.ParseBuf.eat_i128_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_i128_be_panics
/-- `checked_eat_i128_be`: total; with at least 16 bytes, the 16-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_i128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (beNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_i128_be_spec
/-- `eat_f32_le`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte little-endian integer. Panics on fewer (`eat_f32_le_panics`). -/
recall io.ParseBuf.eat_f32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f32_le_spec
/-- `eat_f32_le` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_f32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_f32_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f32_le_panics
/-- `checked_eat_f32_le`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_f32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_f32_le_spec
/-- `eat_f32_be`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte big-endian integer. Panics on fewer (`eat_f32_be_panics`). -/
recall io.ParseBuf.eat_f32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f32_be_spec
/-- `eat_f32_be` panics on a buffer of fewer than 4 bytes. -/
recall io.ParseBuf.eat_f32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    io.ParseBuf.eat_f32_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f32_be_panics
/-- `checked_eat_f32_be`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_f32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_f32_be_spec
/-- `eat_f64_le`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte little-endian integer. Panics on fewer (`eat_f64_le_panics`). -/
recall io.ParseBuf.eat_f64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f64_le_spec
/-- `eat_f64_le` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_f64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_f64_le buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f64_le_panics
/-- `checked_eat_f64_le`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_f64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_f64_le_spec
/-- `eat_f64_be`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte big-endian integer. Panics on fewer (`eat_f64_be_panics`). -/
recall io.ParseBuf.eat_f64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f64_be_spec
/-- `eat_f64_be` panics on a buffer of fewer than 8 bytes. -/
recall io.ParseBuf.eat_f64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.eat_f64_be buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_f64_be_panics
/-- `checked_eat_f64_be`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
recall io.ParseBuf.checked_eat_f64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_f64_be_spec
/-- `eat_lenenc_int`: the length-encoded integer at the head of the buffer, as
    `checkedLenencInt` describes it (protocol decoding, plus the documented quirk that `0xFB` and
    `0xFF` give `0`). Panics exactly when `checked_eat_lenenc_int` would return `None` (this and
    `eat_lenenc_int_panics`). -/
recall io.ParseBuf.eat_lenenc_int_spec (buf : io.ParseBuf) (h : (checkedLenencInt buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_int buf ⦃ n rest => (some n.val, rest.val) = checkedLenencInt buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_lenenc_int_spec
/-- `eat_lenenc_int` panics when `checked_eat_lenenc_int` would return `None` (empty or truncated input). -/
recall io.ParseBuf.eat_lenenc_int_panics (buf : io.ParseBuf) (h : (checkedLenencInt buf.val).1 = none) :
    io.ParseBuf.eat_lenenc_int buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_lenenc_int_panics
/-- `checked_eat_lenenc_int`: total; exactly `checkedLenencInt`. In particular a truncated
    integer gives `None` **after consuming its first byte**, and `0xFB`/`0xFF` give `Some(0)`
    (crate quirk: the protocol does not define these as integers). -/
recall io.ParseBuf.checked_eat_lenenc_int_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencInt buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_lenenc_int_spec
/-- Round trip: `checked_eat_lenenc_int` reads back `lenencInt n`, for every `n : u64`. -/
recall io.ParseBuf.checked_eat_lenenc_int_roundtrip (n : U64) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencInt n.val ++ tail) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest => o = some n ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_lenenc_int_roundtrip
/-- `eat_lenenc_str`: the length-encoded string at the head of the buffer (`checkedLenencStr`).
    Panics exactly when `checked_eat_lenenc_str` would return `None` (this and
    `eat_lenenc_str_panics`). (Its doc says a malformed
    length starting with `0xFF` gives an empty slice: that is the `0xFF`-is-`0` quirk, which applies
    to `0xFB` too.) -/
recall io.ParseBuf.eat_lenenc_str_spec (buf : io.ParseBuf) (h : (checkedLenencStr buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_lenenc_str_spec
/-- `eat_lenenc_str` panics when `checked_eat_lenenc_str` would return `None`. (Needs the 64-bit
    target: on a 32-bit `usize` a length `≥ 2^32` is truncated by `len as usize` and may fit.) -/
recall io.ParseBuf.eat_lenenc_str_panics (h64 : Target64) (buf : io.ParseBuf) (h : (checkedLenencStr buf.val).1 = none) :
    io.ParseBuf.eat_lenenc_str buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_lenenc_str_panics
/-- `checked_eat_lenenc_str`: total; exactly `checkedLenencStr`: `None` after consuming the
    length's first byte if the length is truncated, `None` after consuming the whole length if the
    bytes are missing. (Needs the 64-bit target: on a 32-bit `usize` a length `≥ 2^32` would be
    truncated by `len as usize`.) -/
recall io.ParseBuf.checked_eat_lenenc_str_spec (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_lenenc_str_spec
/-- Round trip: `checked_eat_lenenc_str` reads back `lenencStr s`. -/
recall io.ParseBuf.checked_eat_lenenc_str_roundtrip (s : List U8) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencStr s ++ tail) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest => o.map (·.val) = some s ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_lenenc_str_roundtrip
/-- `eat_u8_str`: a string with a `u8` length prefix. Panics exactly when `checked_eat_u8_str` returns `None` (this and `eat_u8_str_panics`). -/
recall io.ParseBuf.eat_u8_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 1 buf.val).1.isSome) :
    io.ParseBuf.eat_u8_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 1 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u8_str_spec
/-- `eat_u8_str` panics when `checked_eat_u8_str` returns `None`. -/
recall io.ParseBuf.eat_u8_str_panics (buf : io.ParseBuf) (h : (checkedLenPrefixed 1 buf.val).1 = none) :
    io.ParseBuf.eat_u8_str buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u8_str_panics
/-- `checked_eat_u8_str`: total; `checkedLenPrefixed 1` (a missing body gives `None` after consuming the length byte). -/
recall io.ParseBuf.checked_eat_u8_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 1 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u8_str_spec
/-- `eat_u32_str`: a string with a little-endian `u32` length prefix. Panics exactly when `checked_eat_u32_str` returns `None` (this and `eat_u32_str_panics`). -/
recall io.ParseBuf.eat_u32_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 4 buf.val).1.isSome) :
    io.ParseBuf.eat_u32_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 4 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_str_spec
/-- `eat_u32_str` panics when `checked_eat_u32_str` returns `None`. -/
recall io.ParseBuf.eat_u32_str_panics (buf : io.ParseBuf) (h : (checkedLenPrefixed 4 buf.val).1 = none) :
    io.ParseBuf.eat_u32_str buf = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_u32_str_panics
/-- `checked_eat_u32_str`: total; `checkedLenPrefixed 4` (a missing body gives `None` after consuming the 4 length bytes). -/
recall io.ParseBuf.checked_eat_u32_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 4 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.checked_eat_u32_str_spec
/-- `eat_null_str`: total; the bytes before the first `0`, consuming the `0` too; if there is no
    `0`, the whole buffer (documented). -/
recall io.ParseBuf.eat_null_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_null_str buf ⦃ s rest =>
      s.val = beforeZero buf.val ∧ rest.val = buf.val.drop ((beforeZero buf.val).length + 1) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.eat_null_str_spec
end mysql_common
