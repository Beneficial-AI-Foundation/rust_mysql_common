import Defs

/-! Statements for `impl ParseBuf` (spec file: `Specs/Io.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `parse_unchecked::<T>(ctx)` is `T::deserialize(ctx, self)` (generic in `T`; for the
    instances that matter see `Specs/Misc/Raw/*`). Its doc warns that it "may panic if `T::SIZE`
    is some": the fixed-size deserializers (`RawInt<LeU16>`, `[u8; N]`, ...) do not check the
    length, see their specs. -/
theorem io.ParseBuf.parse_unchecked_eq {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) :
    io.ParseBuf.parse_unchecked inst buf ctx = inst.deserialize ctx buf := by
  sorry

/-- `parse` of a type without a fixed size (`T::SIZE = None`) is `T::deserialize`. -/
theorem io.ParseBuf.parse_of_size_none {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx)
    (hs : inst.SIZE = ok none) :
    io.ParseBuf.parse inst buf ctx = inst.deserialize ctx buf := by
  sorry

/-- `parse` of a type of fixed size `n` (`T::SIZE = Some(n)`) on a buffer shorter than `n`:
    an error, and the buffer is unchanged (whatever `T::deserialize` does). -/
theorem io.ParseBuf.parse_of_size_short {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : buf.length < n.val) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `parse` of a type of fixed size `n` on a buffer of at least `n` bytes: `T::deserialize` runs on
    the first `n` bytes (so it cannot panic for lack of input), and exactly `n` bytes are consumed
    whatever it consumes of them (bytes it leaves unread are skipped). Stated for any property
    `P` of the result that `T::deserialize` guarantees on that `n`-byte buffer. -/
theorem io.ParseBuf.parse_of_size {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : n.val ≤ buf.length) (P : Option T → Prop)
    (hd : ∀ sub : io.ParseBuf, sub.val = buf.val.take n.val →
      inst.deserialize ctx sub ⦃ r _ => P (okPart r) ⦄) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => P (okPart r) ∧ rest.val = buf.val.drop n.val ⦄ := by
  sorry

/-- `is_empty`: whether the buffer is empty. -/
theorem io.ParseBuf.is_empty_spec (buf : io.ParseBuf) :
    io.ParseBuf.is_empty buf ⦃ b => (b ↔ buf.val = []) ⦄ := by
  sorry

/-- `len`: the number of bytes in the buffer. -/
theorem io.ParseBuf.len_spec (buf : io.ParseBuf) :
    io.ParseBuf.len buf ⦃ n => n.val = buf.length ⦄ := by
  sorry

/-- `skip(cnt)`: drops the first `cnt` bytes. Panics if `cnt > len`. -/
theorem io.ParseBuf.skip_spec (buf : io.ParseBuf) (cnt : Usize) (h : cnt.val ≤ buf.length) :
    io.ParseBuf.skip buf cnt ⦃ rest => rest.val = buf.val.drop cnt.val ⦄ := by
  sorry

/-- `checked_skip(cnt)`: total; `true` and drops `cnt` bytes if there are that many, else `false` and the buffer is unchanged. -/
theorem io.ParseBuf.checked_skip_spec (buf : io.ParseBuf) (cnt : Usize) :
    io.ParseBuf.checked_skip buf cnt ⦃ b rest =>
      if cnt.val ≤ buf.length then b = true ∧ rest.val = buf.val.drop cnt.val
      else b = false ∧ rest = buf ⦄ := by
  sorry

/-- `eat(n)`: splits off the first `n` bytes. Panics if `n > len` (documented). -/
theorem io.ParseBuf.eat_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  sorry

/-- `eat_buf(n)`: as `eat`, returning a `ParseBuf`. -/
theorem io.ParseBuf.eat_buf_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat_buf buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  sorry

/-- `checked_eat(n)`: total; `eat(n)` if there are `n` bytes, else `None` and the buffer is unchanged. -/
theorem io.ParseBuf.checked_eat_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `checked_eat_buf(n)`: as `checked_eat`, returning a `ParseBuf`. -/
theorem io.ParseBuf.checked_eat_buf_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat_buf buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_all`: total; returns the whole buffer and leaves it empty. -/
theorem io.ParseBuf.eat_all_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_all buf ⦃ s rest => s.val = buf.val ∧ rest.val = [] ⦄ := by
  sorry

/-- `eat_u8`: consumes 1 bytes from the head of the buffer and returns the 1-byte little-endian unsigned integer. Panics on fewer than 1 bytes. -/
theorem io.ParseBuf.eat_u8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_u8 buf ⦃ x rest =>
      x.val = leNat (buf.val.take 1) ∧ rest.val = buf.val.drop 1 ⦄ := by
  sorry

/-- `checked_eat_u8`: total; with at least 1 bytes, the 1-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i8`: consumes 1 bytes from the head of the buffer and returns the 1-byte little-endian two's-complement integer. Panics on fewer than 1 bytes. -/
theorem io.ParseBuf.eat_i8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_i8 buf ⦃ x rest =>
      x.val = toSigned 8 (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄ := by
  sorry

/-- `checked_eat_i8`: total; with at least 1 bytes, the 1-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian unsigned integer. Panics on fewer than 2 bytes. -/
theorem io.ParseBuf.eat_u16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `checked_eat_u16_le`: total; with at least 2 bytes, the 2-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian two's-complement integer. Panics on fewer than 2 bytes. -/
theorem io.ParseBuf.eat_i16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_le buf ⦃ x rest =>
      x.val = toSigned 16 (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `checked_eat_i16_le`: total; with at least 2 bytes, the 2-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian unsigned integer. Panics on fewer than 2 bytes. -/
theorem io.ParseBuf.eat_u16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `checked_eat_u16_be`: total; with at least 2 bytes, the 2-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian two's-complement integer. Panics on fewer than 2 bytes. -/
theorem io.ParseBuf.eat_i16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_be buf ⦃ x rest =>
      x.val = toSigned 16 (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  sorry

/-- `checked_eat_i16_be`: total; with at least 2 bytes, the 2-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (beNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian unsigned integer. Panics on fewer than 3 bytes. -/
theorem io.ParseBuf.eat_u24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `checked_eat_u24_le`: total; with at least 3 bytes, the 3-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian integer, zero-extended. Panics on fewer than 3 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
theorem io.ParseBuf.eat_i24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `checked_eat_i24_le`: total; with at least 3 bytes, the 3-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
theorem io.ParseBuf.checked_eat_i24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian unsigned integer. Panics on fewer than 3 bytes. -/
theorem io.ParseBuf.eat_u24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `checked_eat_u24_be`: total; with at least 3 bytes, the 3-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian integer, zero-extended. Panics on fewer than 3 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄ := by
  sorry

/-- `checked_eat_i24_be`: total; with at least 3 bytes, the 3-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian unsigned integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_u32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_u32_le`: total; with at least 4 bytes, the 4-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian two's-complement integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_i32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_le buf ⦃ x rest =>
      x.val = toSigned 32 (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_i32_le`: total; with at least 4 bytes, the 4-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian unsigned integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_u32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_u32_be`: total; with at least 4 bytes, the 4-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian two's-complement integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_i32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_be buf ⦃ x rest =>
      x.val = toSigned 32 (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_i32_be`: total; with at least 4 bytes, the 4-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (beNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian unsigned integer. Panics on fewer than 5 bytes. -/
theorem io.ParseBuf.eat_u40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄ := by
  sorry

/-- `checked_eat_u40_le`: total; with at least 5 bytes, the 5-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian integer, zero-extended. Panics on fewer than 5 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄ := by
  sorry

/-- `checked_eat_i40_le`: total; with at least 5 bytes, the 5-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian unsigned integer. Panics on fewer than 5 bytes. -/
theorem io.ParseBuf.eat_u40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄ := by
  sorry

/-- `checked_eat_u40_be`: total; with at least 5 bytes, the 5-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian integer, zero-extended. Panics on fewer than 5 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄ := by
  sorry

/-- `checked_eat_i40_be`: total; with at least 5 bytes, the 5-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian unsigned integer. Panics on fewer than 6 bytes. -/
theorem io.ParseBuf.eat_u48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄ := by
  sorry

/-- `checked_eat_u48_le`: total; with at least 6 bytes, the 6-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian integer, zero-extended. Panics on fewer than 6 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄ := by
  sorry

/-- `checked_eat_i48_le`: total; with at least 6 bytes, the 6-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian unsigned integer. Panics on fewer than 6 bytes. -/
theorem io.ParseBuf.eat_u48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄ := by
  sorry

/-- `checked_eat_u48_be`: total; with at least 6 bytes, the 6-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian integer, zero-extended. Panics on fewer than 6 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄ := by
  sorry

/-- `checked_eat_i48_be`: total; with at least 6 bytes, the 6-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian unsigned integer. Panics on fewer than 7 bytes. -/
theorem io.ParseBuf.eat_u56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄ := by
  sorry

/-- `checked_eat_u56_le`: total; with at least 7 bytes, the 7-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian integer, zero-extended. Panics on fewer than 7 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
theorem io.ParseBuf.eat_i56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄ := by
  sorry

/-- `checked_eat_i56_le`: total; with at least 7 bytes, the 7-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
theorem io.ParseBuf.checked_eat_i56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian unsigned integer. Panics on fewer than 7 bytes. -/
theorem io.ParseBuf.eat_u56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄ := by
  sorry

/-- `checked_eat_u56_be`: total; with at least 7 bytes, the 7-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian integer, zero-extended. Panics on fewer than 7 bytes. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.eat_i56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄ := by
  sorry

/-- `checked_eat_i56_be`: total; with at least 7 bytes, the 7-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. bytes `FF FF FF` give `16777215`, not `-1`. -/
theorem io.ParseBuf.checked_eat_i56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian unsigned integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_u64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_u64_le`: total; with at least 8 bytes, the 8-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian two's-complement integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_i64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_le buf ⦃ x rest =>
      x.val = toSigned 64 (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_i64_le`: total; with at least 8 bytes, the 8-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian unsigned integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_u64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_u64_be`: total; with at least 8 bytes, the 8-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian two's-complement integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_i64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_be buf ⦃ x rest =>
      x.val = toSigned 64 (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_i64_be`: total; with at least 8 bytes, the 8-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (beNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian unsigned integer. Panics on fewer than 16 bytes. -/
theorem io.ParseBuf.eat_u128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `checked_eat_u128_le`: total; with at least 16 bytes, the 16-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian two's-complement integer. Panics on fewer than 16 bytes. -/
theorem io.ParseBuf.eat_i128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_le buf ⦃ x rest =>
      x.val = toSigned 128 (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `checked_eat_i128_le`: total; with at least 16 bytes, the 16-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (leNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_u128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian unsigned integer. Panics on fewer than 16 bytes. -/
theorem io.ParseBuf.eat_u128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `checked_eat_u128_be`: total; with at least 16 bytes, the 16-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_u128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_i128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian two's-complement integer. Panics on fewer than 16 bytes. -/
theorem io.ParseBuf.eat_i128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_be buf ⦃ x rest =>
      x.val = toSigned 128 (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `checked_eat_i128_be`: total; with at least 16 bytes, the 16-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_i128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (beNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_f32_le`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte little-endian integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_f32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_f32_le`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_f32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_f32_be`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte big-endian integer. Panics on fewer than 4 bytes. -/
theorem io.ParseBuf.eat_f32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `checked_eat_f32_be`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_f32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_f64_le`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte little-endian integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_f64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_f64_le`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_f64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_f64_be`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte big-endian integer. Panics on fewer than 8 bytes. -/
theorem io.ParseBuf.eat_f64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `checked_eat_f64_be`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
theorem io.ParseBuf.checked_eat_f64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  sorry

/-- `eat_lenenc_int`: the length-encoded integer at the head of the buffer, as
    `checkedLenencInt` describes it (protocol decoding, plus the documented quirk that `0xFB` and
    `0xFF` give `0`). Panics exactly when `checked_eat_lenenc_int` would return `None`. -/
theorem io.ParseBuf.eat_lenenc_int_spec (buf : io.ParseBuf) (h : (checkedLenencInt buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_int buf ⦃ n rest => (some n.val, rest.val) = checkedLenencInt buf.val ⦄ := by
  sorry

/-- `checked_eat_lenenc_int`: total; exactly `checkedLenencInt`. In particular a truncated
    integer gives `None` **after consuming its first byte**, and `0xFB`/`0xFF` give `Some(0)`
    (crate quirk: the protocol does not define these as integers). -/
theorem io.ParseBuf.checked_eat_lenenc_int_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencInt buf.val ⦄ := by
  sorry

/-- Round trip: `checked_eat_lenenc_int` reads back `lenencInt n`, for every `n : u64`. -/
theorem io.ParseBuf.checked_eat_lenenc_int_roundtrip (n : U64) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencInt n.val ++ tail) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest => o = some n ∧ rest.val = tail ⦄ := by
  sorry

/-- `eat_lenenc_str`: the length-encoded string at the head of the buffer (`checkedLenencStr`).
    Panics exactly when `checked_eat_lenenc_str` would return `None`. (Its doc says a malformed
    length starting with `0xFF` gives an empty slice: that is the `0xFF`-is-`0` quirk, which applies
    to `0xFB` too.) -/
theorem io.ParseBuf.eat_lenenc_str_spec (buf : io.ParseBuf) (h : (checkedLenencStr buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenencStr buf.val ⦄ := by
  sorry

/-- `checked_eat_lenenc_str`: total; exactly `checkedLenencStr`: `None` after consuming the
    length's first byte if the length is truncated, `None` after consuming the whole length if the
    bytes are missing. (Needs the 64-bit target: on a 32-bit `usize` a length `≥ 2^32` would be
    truncated by `len as usize`.) -/
theorem io.ParseBuf.checked_eat_lenenc_str_spec (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencStr buf.val ⦄ := by
  sorry

/-- Round trip: `checked_eat_lenenc_str` reads back `lenencStr s`. -/
theorem io.ParseBuf.checked_eat_lenenc_str_roundtrip (s : List U8) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencStr s ++ tail) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest => o.map (·.val) = some s ∧ rest.val = tail ⦄ := by
  sorry

/-- `eat_u8_str`: a string with a `u8` length prefix. Panics exactly when `checked_eat_u8_str` returns `None`. -/
theorem io.ParseBuf.eat_u8_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 1 buf.val).1.isSome) :
    io.ParseBuf.eat_u8_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  sorry

/-- `checked_eat_u8_str`: total; `checkedLenPrefixed 1` (a missing body gives `None` after consuming the length byte). -/
theorem io.ParseBuf.checked_eat_u8_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  sorry

/-- `eat_u32_str`: a string with a little-endian `u32` length prefix. Panics exactly when `checked_eat_u32_str` returns `None`. -/
theorem io.ParseBuf.eat_u32_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 4 buf.val).1.isSome) :
    io.ParseBuf.eat_u32_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  sorry

/-- `checked_eat_u32_str`: total; `checkedLenPrefixed 4` (a missing body gives `None` after consuming the 4 length bytes). -/
theorem io.ParseBuf.checked_eat_u32_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  sorry

/-- `eat_null_str`: total; the bytes before the first `0`, consuming the `0` too; if there is no
    `0`, the whole buffer (documented). -/
theorem io.ParseBuf.eat_null_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_null_str buf ⦃ s rest =>
      s.val = beforeZero buf.val ∧ rest.val = buf.val.drop ((beforeZero buf.val).length + 1) ⦄ := by
  sorry

end mysql_common
