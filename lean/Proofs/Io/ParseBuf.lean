import Defs
import Proofs.Util.ParseBuf

/-! Statements for `impl ParseBuf` (spec file: `Specs/Io.lean`). Helper lemmas: `Proofs/Util/ParseBuf.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `parse_unchecked::<T>(ctx)` is `T::deserialize(ctx, self)` (generic in `T`; for the
    instances that matter see `Specs/Misc/Raw/*`). Its doc warns that it "may panic if `T::SIZE`
    is some": the fixed-size deserializers (`RawInt<LeU16>`, `[u8; N]`, ...) do not check the
    length, see their specs. -/
theorem io.ParseBuf.parse_unchecked_eq {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) :
    io.ParseBuf.parse_unchecked inst buf ctx = inst.deserialize ctx buf := by
  rfl

/-- `parse` of a type without a fixed size (`T::SIZE = None`) is `T::deserialize`. -/
theorem io.ParseBuf.parse_of_size_none {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx)
    (hs : inst.SIZE = ok none) :
    io.ParseBuf.parse inst buf ctx = inst.deserialize ctx buf := by
  simp [io.ParseBuf.parse, hs, io.ParseBuf.parse_unchecked]

/-- `parse` of a type of fixed size `n` (`T::SIZE = Some(n)`) on a buffer shorter than `n`:
    an error, and the buffer is unchanged (whatever `T::deserialize` does). -/
theorem io.ParseBuf.parse_of_size_short {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : buf.length < n.val) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => okPart r = none ∧ rest = buf ⦄ := by
  simp only [io.ParseBuf.parse, hs, io.ParseBuf.parse_unchecked]
  step*
  all_goals (cases r <;> simp_all [okPart] <;> omega)

/-- `parse` of a type of fixed size `n` on a buffer of at least `n` bytes: `T::deserialize` runs on
    the first `n` bytes (so it cannot panic for lack of input), and exactly `n` bytes are consumed
    whatever it consumes of them (bytes it leaves unread are skipped). Stated for any property
    `P` of the result that `T::deserialize` guarantees on that `n`-byte buffer. -/
theorem io.ParseBuf.parse_of_size {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (buf : io.ParseBuf) (ctx : Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (hlen : n.val ≤ buf.length) (P : Option T → Prop)
    (hd : ∀ sub : io.ParseBuf, sub.val = buf.val.take n.val →
      inst.deserialize ctx sub ⦃ r _ => P (okPart r) ⦄) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest => P (okPart r) ∧ rest.val = buf.val.drop n.val ⦄ := by
  simp only [io.ParseBuf.parse, hs, io.ParseBuf.parse_unchecked]
  step*
  all_goals (cases r <;> simp_all [okPart])

/-- `is_empty`: whether the buffer is empty. -/
theorem io.ParseBuf.is_empty_spec (buf : io.ParseBuf) :
    io.ParseBuf.is_empty buf ⦃ b => (b ↔ buf.val = []) ⦄ := by
  unfold io.ParseBuf.is_empty; step*; simp only [decide_eq_true_eq, UScalar.eq_equiv]; rw [← List.length_eq_zero_iff]; simp_all [Slice.length]

/-- `len`: the number of bytes in the buffer. -/
theorem io.ParseBuf.len_spec (buf : io.ParseBuf) :
    io.ParseBuf.len buf ⦃ n => n.val = buf.length ⦄ := by
  exact len_ok buf

/-- `skip(cnt)`: drops the first `cnt` bytes. Panics if `cnt > len` (`skip_panics`). -/
@[step]
theorem io.ParseBuf.skip_spec (buf : io.ParseBuf) (cnt : Usize) (h : cnt.val ≤ buf.length) :
    io.ParseBuf.skip buf cnt ⦃ rest => rest.val = buf.val.drop cnt.val ⦄ := by
  unfold io.ParseBuf.skip
  simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, h]

/-- `skip(cnt)` panics if `cnt > len`. -/
theorem io.ParseBuf.skip_panics (buf : io.ParseBuf) (cnt : Usize) (h : buf.length < cnt.val) :
    ¬ io.ParseBuf.skip buf cnt ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.skip
  simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, show ¬ cnt.val ≤ buf.length by omega]

/-- `checked_skip(cnt)`: total; `true` and drops `cnt` bytes if there are that many, else `false` and the buffer is unchanged. -/
theorem io.ParseBuf.checked_skip_spec (buf : io.ParseBuf) (cnt : Usize) :
    io.ParseBuf.checked_skip buf cnt ⦃ b rest =>
      if cnt.val ≤ buf.length then b = true ∧ rest.val = buf.val.drop cnt.val
      else b = false ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_skip
  step*
  all_goals split_ifs <;> simp_all

/-- `eat(n)`: splits off the first `n` bytes. Panics if `n > len` (documented; `eat_panics`). -/
theorem io.ParseBuf.eat_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  exact eat_ok buf n h

/-- `eat(n)` panics if `n > len` (documented). -/
theorem io.ParseBuf.eat_panics (buf : io.ParseBuf) (n : Usize) (h : buf.length < n.val) :
    ¬ io.ParseBuf.eat buf n ⦃ _ => True ⦄ := by
  exact eat_fail buf n h

/-- `eat_buf(n)`: as `eat`, returning a `ParseBuf`. -/
theorem io.ParseBuf.eat_buf_spec (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat_buf buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  unfold io.ParseBuf.eat_buf
  step*

/-- `eat_buf(n)` panics if `n > len`. -/
theorem io.ParseBuf.eat_buf_panics (buf : io.ParseBuf) (n : Usize) (h : buf.length < n.val) :
    ¬ io.ParseBuf.eat_buf buf n ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_buf, io.ParseBuf.eat, core.slice.Slice.split_at, show ¬ n.val ≤ buf.length by omega]

/-- `checked_eat(n)`: total; `eat(n)` if there are `n` bytes, else `None` and the buffer is unchanged. -/
theorem io.ParseBuf.checked_eat_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  exact checked_eat_ok buf n

/-- `checked_eat_buf(n)`: as `checked_eat`, returning a `ParseBuf`. -/
theorem io.ParseBuf.checked_eat_buf_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat_buf buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  exact checked_eat_buf_ok buf n

/-- `eat_all`: total; returns the whole buffer and leaves it empty. -/
theorem io.ParseBuf.eat_all_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_all buf ⦃ s rest => s.val = buf.val ∧ rest.val = [] ⦄ := by
  unfold io.ParseBuf.eat_all
  step*
  simp_all

/-- `eat_u8`: consumes 1 byte from the head of the buffer and returns the 1-byte little-endian unsigned integer. Panics on fewer (`eat_u8_panics`). -/
@[step]
theorem io.ParseBuf.eat_u8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_u8 buf ⦃ x rest =>
      x.val = leNat (buf.val.take 1) ∧ rest.val = buf.val.drop 1 ⦄ := by
  unfold io.ParseBuf.eat_u8
  simp only [io.ParseBuf.eat_u8.SIZE]
  step*
  pb_finish

/-- `eat_u8` panics on a buffer of fewer than 1 byte. -/
theorem io.ParseBuf.eat_u8_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ io.ParseBuf.eat_u8 buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u8, io.ParseBuf.eat_u8.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (1 ≤ buf.length) by omega]

/-- `checked_eat_u8`: total; with at least 1 byte, the 1-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u8
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i8`: consumes 1 byte from the head of the buffer and returns the 1-byte little-endian two's-complement integer. Panics on fewer (`eat_i8_panics`). -/
@[step]
theorem io.ParseBuf.eat_i8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.eat_i8 buf ⦃ x rest =>
      x.val = toSigned 8 (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄ := by
  unfold io.ParseBuf.eat_i8
  simp only [io.ParseBuf.eat_i8.SIZE]
  step*
  pb_finish

/-- `eat_i8` panics on a buffer of fewer than 1 byte. -/
theorem io.ParseBuf.eat_i8_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ io.ParseBuf.eat_i8 buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i8, io.ParseBuf.eat_i8.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (1 ≤ buf.length) by omega]

/-- `checked_eat_i8`: total; with at least 1 byte, the 1-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i8_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i8 buf ⦃ o rest =>
      if 1 ≤ buf.length then o.map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i8
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian unsigned integer. Panics on fewer (`eat_u16_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold io.ParseBuf.eat_u16_le
  simp only [io.ParseBuf.eat_u16_le.SIZE]
  step*
  pb_finish

/-- `eat_u16_le` panics on a buffer of fewer than 2 bytes. -/
theorem io.ParseBuf.eat_u16_le_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ io.ParseBuf.eat_u16_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u16_le, io.ParseBuf.eat_u16_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (2 ≤ buf.length) by omega]

/-- `checked_eat_u16_le`: total; with at least 2 bytes, the 2-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u16_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i16_le`: consumes 2 bytes from the head of the buffer and returns the 2-byte little-endian two's-complement integer. Panics on fewer (`eat_i16_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_i16_le_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_le buf ⦃ x rest =>
      x.val = toSigned 16 (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold io.ParseBuf.eat_i16_le
  simp only [io.ParseBuf.eat_i16_le.SIZE]
  step*
  pb_finish

/-- `eat_i16_le` panics on a buffer of fewer than 2 bytes. -/
theorem io.ParseBuf.eat_i16_le_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ io.ParseBuf.eat_i16_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i16_le, io.ParseBuf.eat_i16_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (2 ≤ buf.length) by omega]

/-- `checked_eat_i16_le`: total; with at least 2 bytes, the 2-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i16_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_le buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i16_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian unsigned integer. Panics on fewer (`eat_u16_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_u16_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold io.ParseBuf.eat_u16_be
  simp only [io.ParseBuf.eat_u16_be.SIZE]
  step*
  pb_finish

/-- `eat_u16_be` panics on a buffer of fewer than 2 bytes. -/
theorem io.ParseBuf.eat_u16_be_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ io.ParseBuf.eat_u16_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u16_be, io.ParseBuf.eat_u16_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (2 ≤ buf.length) by omega]

/-- `checked_eat_u16_be`: total; with at least 2 bytes, the 2-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u16_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i16_be`: consumes 2 bytes from the head of the buffer and returns the 2-byte big-endian two's-complement integer. Panics on fewer (`eat_i16_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_i16_be_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.eat_i16_be buf ⦃ x rest =>
      x.val = toSigned 16 (beNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  unfold io.ParseBuf.eat_i16_be
  simp only [io.ParseBuf.eat_i16_be.SIZE]
  step*
  pb_finish

/-- `eat_i16_be` panics on a buffer of fewer than 2 bytes. -/
theorem io.ParseBuf.eat_i16_be_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ io.ParseBuf.eat_i16_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i16_be, io.ParseBuf.eat_i16_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (2 ≤ buf.length) by omega]

/-- `checked_eat_i16_be`: total; with at least 2 bytes, the 2-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i16_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i16_be buf ⦃ o rest =>
      if 2 ≤ buf.length then o.map (·.val) = some (toSigned 16 (beNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i16_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian unsigned integer. Panics on fewer (`eat_u24_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄ := by
  unfold io.ParseBuf.eat_u24_le
  simp only [io.ParseBuf.eat_u24_le.SIZE]
  step*
  pb_finish

/-- `eat_u24_le` panics on a buffer of fewer than 3 bytes. -/
theorem io.ParseBuf.eat_u24_le_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ io.ParseBuf.eat_u24_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u24_le, io.ParseBuf.eat_u24_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (3 ≤ buf.length) by omega]

/-- `checked_eat_u24_le`: total; with at least 3 bytes, the 3-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u24_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i24_le`: consumes 3 bytes from the head of the buffer and returns the 3-byte little-endian integer, zero-extended. Panics on fewer (`eat_i24_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
@[step]
theorem io.ParseBuf.eat_i24_le_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄ := by
  unfold io.ParseBuf.eat_i24_le
  simp only [io.ParseBuf.eat_i24_le.SIZE]
  step*
  pb_finish

/-- `eat_i24_le` panics on a buffer of fewer than 3 bytes. -/
theorem io.ParseBuf.eat_i24_le_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ io.ParseBuf.eat_i24_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i24_le, io.ParseBuf.eat_i24_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (3 ≤ buf.length) by omega]

/-- `checked_eat_i24_le`: total; with at least 3 bytes, the 3-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. So `put_i24_le` then this reader does not round-trip negative values. -/
@[step]
theorem io.ParseBuf.checked_eat_i24_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_le buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i24_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian unsigned integer. Panics on fewer (`eat_u24_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_u24_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 3) ∧ rest.val = buf.val.drop 3 ⦄ := by
  unfold io.ParseBuf.eat_u24_be
  simp only [io.ParseBuf.eat_u24_be.SIZE]
  step*
  pb_finish

/-- `eat_u24_be` panics on a buffer of fewer than 3 bytes. -/
theorem io.ParseBuf.eat_u24_be_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ io.ParseBuf.eat_u24_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u24_be, io.ParseBuf.eat_u24_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (3 ≤ buf.length) by omega]

/-- `checked_eat_u24_be`: total; with at least 3 bytes, the 3-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u24_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i24_be`: consumes 3 bytes from the head of the buffer and returns the 3-byte big-endian integer, zero-extended. Panics on fewer (`eat_i24_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i24_be_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.eat_i24_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 3) : Nat) : Int) ∧ rest.val = buf.val.drop 3 ⦄ := by
  unfold io.ParseBuf.eat_i24_be
  simp only [io.ParseBuf.eat_i24_be.SIZE]
  step*
  pb_finish

/-- `eat_i24_be` panics on a buffer of fewer than 3 bytes. -/
theorem io.ParseBuf.eat_i24_be_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ io.ParseBuf.eat_i24_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i24_be, io.ParseBuf.eat_i24_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (3 ≤ buf.length) by omega]

/-- `checked_eat_i24_be`: total; with at least 3 bytes, the 3-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 3 bytes `FF` give `2^24 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i24_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i24_be buf ⦃ o rest =>
      if 3 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i24_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian unsigned integer. Panics on fewer (`eat_u32_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_u32_le
  simp only [io.ParseBuf.eat_u32_le.SIZE]
  step*
  pb_finish

/-- `eat_u32_le` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_u32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_u32_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u32_le, io.ParseBuf.eat_u32_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_u32_le`: total; with at least 4 bytes, the 4-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u32_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i32_le`: consumes 4 bytes from the head of the buffer and returns the 4-byte little-endian two's-complement integer. Panics on fewer (`eat_i32_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_i32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_le buf ⦃ x rest =>
      x.val = toSigned 32 (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_i32_le
  simp only [io.ParseBuf.eat_i32_le.SIZE]
  step*
  pb_finish

/-- `eat_i32_le` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_i32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_i32_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i32_le, io.ParseBuf.eat_i32_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_i32_le`: total; with at least 4 bytes, the 4-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i32_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian unsigned integer. Panics on fewer (`eat_u32_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_u32_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_u32_be
  simp only [io.ParseBuf.eat_u32_be.SIZE]
  step*
  pb_finish

/-- `eat_u32_be` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_u32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_u32_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u32_be, io.ParseBuf.eat_u32_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_u32_be`: total; with at least 4 bytes, the 4-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u32_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i32_be`: consumes 4 bytes from the head of the buffer and returns the 4-byte big-endian two's-complement integer. Panics on fewer (`eat_i32_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_i32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_i32_be buf ⦃ x rest =>
      x.val = toSigned 32 (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_i32_be
  simp only [io.ParseBuf.eat_i32_be.SIZE]
  step*
  pb_finish

/-- `eat_i32_be` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_i32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_i32_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i32_be, io.ParseBuf.eat_i32_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_i32_be`: total; with at least 4 bytes, the 4-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.val) = some (toSigned 32 (beNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i32_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian unsigned integer. Panics on fewer (`eat_u40_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄ := by
  unfold io.ParseBuf.eat_u40_le
  simp only [io.ParseBuf.eat_u40_le.SIZE]
  step*
  pb_finish

/-- `eat_u40_le` panics on a buffer of fewer than 5 bytes. -/
theorem io.ParseBuf.eat_u40_le_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    ¬ io.ParseBuf.eat_u40_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u40_le, io.ParseBuf.eat_u40_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (5 ≤ buf.length) by omega]

/-- `checked_eat_u40_le`: total; with at least 5 bytes, the 5-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u40_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i40_le`: consumes 5 bytes from the head of the buffer and returns the 5-byte little-endian integer, zero-extended. Panics on fewer (`eat_i40_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i40_le_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄ := by
  unfold io.ParseBuf.eat_i40_le
  simp only [io.ParseBuf.eat_i40_le.SIZE]
  step*
  pb_finish

/-- `eat_i40_le` panics on a buffer of fewer than 5 bytes. -/
theorem io.ParseBuf.eat_i40_le_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    ¬ io.ParseBuf.eat_i40_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i40_le, io.ParseBuf.eat_i40_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (5 ≤ buf.length) by omega]

/-- `checked_eat_i40_le`: total; with at least 5 bytes, the 5-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i40_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_le buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i40_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian unsigned integer. Panics on fewer (`eat_u40_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_u40_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 5) ∧ rest.val = buf.val.drop 5 ⦄ := by
  unfold io.ParseBuf.eat_u40_be
  simp only [io.ParseBuf.eat_u40_be.SIZE]
  step*
  pb_finish

/-- `eat_u40_be` panics on a buffer of fewer than 5 bytes. -/
theorem io.ParseBuf.eat_u40_be_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    ¬ io.ParseBuf.eat_u40_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u40_be, io.ParseBuf.eat_u40_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (5 ≤ buf.length) by omega]

/-- `checked_eat_u40_be`: total; with at least 5 bytes, the 5-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 5)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u40_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i40_be`: consumes 5 bytes from the head of the buffer and returns the 5-byte big-endian integer, zero-extended. Panics on fewer (`eat_i40_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i40_be_spec (buf : io.ParseBuf) (h : 5 ≤ buf.length) :
    io.ParseBuf.eat_i40_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 5) : Nat) : Int) ∧ rest.val = buf.val.drop 5 ⦄ := by
  unfold io.ParseBuf.eat_i40_be
  simp only [io.ParseBuf.eat_i40_be.SIZE]
  step*
  pb_finish

/-- `eat_i40_be` panics on a buffer of fewer than 5 bytes. -/
theorem io.ParseBuf.eat_i40_be_panics (buf : io.ParseBuf) (h : buf.length < 5) :
    ¬ io.ParseBuf.eat_i40_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i40_be, io.ParseBuf.eat_i40_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (5 ≤ buf.length) by omega]

/-- `checked_eat_i40_be`: total; with at least 5 bytes, the 5-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 5 bytes `FF` give `2^40 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i40_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i40_be buf ⦃ o rest =>
      if 5 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 5) : Nat) : Int)) ∧ rest.val = buf.val.drop 5
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i40_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian unsigned integer. Panics on fewer (`eat_u48_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄ := by
  unfold io.ParseBuf.eat_u48_le
  simp only [io.ParseBuf.eat_u48_le.SIZE]
  step*
  pb_finish

/-- `eat_u48_le` panics on a buffer of fewer than 6 bytes. -/
theorem io.ParseBuf.eat_u48_le_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    ¬ io.ParseBuf.eat_u48_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u48_le, io.ParseBuf.eat_u48_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (6 ≤ buf.length) by omega]

/-- `checked_eat_u48_le`: total; with at least 6 bytes, the 6-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u48_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i48_le`: consumes 6 bytes from the head of the buffer and returns the 6-byte little-endian integer, zero-extended. Panics on fewer (`eat_i48_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i48_le_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄ := by
  unfold io.ParseBuf.eat_i48_le
  simp only [io.ParseBuf.eat_i48_le.SIZE]
  step*
  pb_finish

/-- `eat_i48_le` panics on a buffer of fewer than 6 bytes. -/
theorem io.ParseBuf.eat_i48_le_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    ¬ io.ParseBuf.eat_i48_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i48_le, io.ParseBuf.eat_i48_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (6 ≤ buf.length) by omega]

/-- `checked_eat_i48_le`: total; with at least 6 bytes, the 6-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i48_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_le buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i48_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian unsigned integer. Panics on fewer (`eat_u48_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_u48_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 6) ∧ rest.val = buf.val.drop 6 ⦄ := by
  unfold io.ParseBuf.eat_u48_be
  simp only [io.ParseBuf.eat_u48_be.SIZE]
  step*
  pb_finish

/-- `eat_u48_be` panics on a buffer of fewer than 6 bytes. -/
theorem io.ParseBuf.eat_u48_be_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    ¬ io.ParseBuf.eat_u48_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u48_be, io.ParseBuf.eat_u48_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (6 ≤ buf.length) by omega]

/-- `checked_eat_u48_be`: total; with at least 6 bytes, the 6-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u48_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i48_be`: consumes 6 bytes from the head of the buffer and returns the 6-byte big-endian integer, zero-extended. Panics on fewer (`eat_i48_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i48_be_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    io.ParseBuf.eat_i48_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 6) : Nat) : Int) ∧ rest.val = buf.val.drop 6 ⦄ := by
  unfold io.ParseBuf.eat_i48_be
  simp only [io.ParseBuf.eat_i48_be.SIZE]
  step*
  pb_finish

/-- `eat_i48_be` panics on a buffer of fewer than 6 bytes. -/
theorem io.ParseBuf.eat_i48_be_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    ¬ io.ParseBuf.eat_i48_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i48_be, io.ParseBuf.eat_i48_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (6 ≤ buf.length) by omega]

/-- `checked_eat_i48_be`: total; with at least 6 bytes, the 6-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 6 bytes `FF` give `2^48 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i48_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i48_be buf ⦃ o rest =>
      if 6 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 6) : Nat) : Int)) ∧ rest.val = buf.val.drop 6
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i48_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian unsigned integer. Panics on fewer (`eat_u56_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold io.ParseBuf.eat_u56_le
  simp only [io.ParseBuf.eat_u56_le.SIZE]
  step*
  pb_finish

/-- `eat_u56_le` panics on a buffer of fewer than 7 bytes. -/
theorem io.ParseBuf.eat_u56_le_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ io.ParseBuf.eat_u56_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u56_le, io.ParseBuf.eat_u56_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (7 ≤ buf.length) by omega]

/-- `checked_eat_u56_le`: total; with at least 7 bytes, the 7-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u56_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i56_le`: consumes 7 bytes from the head of the buffer and returns the 7-byte little-endian integer, zero-extended. Panics on fewer (`eat_i56_le_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
@[step]
theorem io.ParseBuf.eat_i56_le_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_le buf ⦃ x rest =>
      x.val = ((leNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold io.ParseBuf.eat_i56_le
  simp only [io.ParseBuf.eat_i56_le.SIZE]
  step*
  pb_finish

/-- `eat_i56_le` panics on a buffer of fewer than 7 bytes. -/
theorem io.ParseBuf.eat_i56_le_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ io.ParseBuf.eat_i56_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i56_le, io.ParseBuf.eat_i56_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (7 ≤ buf.length) by omega]

/-- `checked_eat_i56_le`: total; with at least 7 bytes, the 7-byte little-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. So `put_i56_le` then this reader does not round-trip negative values. -/
@[step]
theorem io.ParseBuf.checked_eat_i56_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_le buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i56_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian unsigned integer. Panics on fewer (`eat_u56_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_u56_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 7) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold io.ParseBuf.eat_u56_be
  simp only [io.ParseBuf.eat_u56_be.SIZE]
  step*
  pb_finish

/-- `eat_u56_be` panics on a buffer of fewer than 7 bytes. -/
theorem io.ParseBuf.eat_u56_be_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ io.ParseBuf.eat_u56_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u56_be, io.ParseBuf.eat_u56_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (7 ≤ buf.length) by omega]

/-- `checked_eat_u56_be`: total; with at least 7 bytes, the 7-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u56_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i56_be`: consumes 7 bytes from the head of the buffer and returns the 7-byte big-endian integer, zero-extended. Panics on fewer (`eat_i56_be_panics`). **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.eat_i56_be_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.eat_i56_be buf ⦃ x rest =>
      x.val = ((beNat (buf.val.take 7) : Nat) : Int) ∧ rest.val = buf.val.drop 7 ⦄ := by
  unfold io.ParseBuf.eat_i56_be
  simp only [io.ParseBuf.eat_i56_be.SIZE]
  step*
  pb_finish

/-- `eat_i56_be` panics on a buffer of fewer than 7 bytes. -/
theorem io.ParseBuf.eat_i56_be_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ io.ParseBuf.eat_i56_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i56_be, io.ParseBuf.eat_i56_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (7 ≤ buf.length) by omega]

/-- `checked_eat_i56_be`: total; with at least 7 bytes, the 7-byte big-endian integer, zero-extended, consumed; else `None`, buffer unchanged. **No sign extension** (the original macro and the patched copy agree): the result is never negative, e.g. 7 bytes `FF` give `2^56 - 1`, not `-1`. -/
@[step]
theorem io.ParseBuf.checked_eat_i56_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i56_be buf ⦃ o rest =>
      if 7 ≤ buf.length then o.map (·.val) = some (((beNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i56_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian unsigned integer. Panics on fewer (`eat_u64_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_u64_le
  simp only [io.ParseBuf.eat_u64_le.SIZE]
  step*
  pb_finish

/-- `eat_u64_le` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_u64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_u64_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u64_le, io.ParseBuf.eat_u64_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_u64_le`: total; with at least 8 bytes, the 8-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u64_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i64_le`: consumes 8 bytes from the head of the buffer and returns the 8-byte little-endian two's-complement integer. Panics on fewer (`eat_i64_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_i64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_le buf ⦃ x rest =>
      x.val = toSigned 64 (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_i64_le
  simp only [io.ParseBuf.eat_i64_le.SIZE]
  step*
  pb_finish

/-- `eat_i64_le` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_i64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_i64_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i64_le, io.ParseBuf.eat_i64_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_i64_le`: total; with at least 8 bytes, the 8-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i64_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian unsigned integer. Panics on fewer (`eat_u64_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_u64_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_u64_be
  simp only [io.ParseBuf.eat_u64_be.SIZE]
  step*
  pb_finish

/-- `eat_u64_be` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_u64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_u64_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u64_be, io.ParseBuf.eat_u64_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_u64_be`: total; with at least 8 bytes, the 8-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u64_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i64_be`: consumes 8 bytes from the head of the buffer and returns the 8-byte big-endian two's-complement integer. Panics on fewer (`eat_i64_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_i64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_i64_be buf ⦃ x rest =>
      x.val = toSigned 64 (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_i64_be
  simp only [io.ParseBuf.eat_i64_be.SIZE]
  step*
  pb_finish

/-- `eat_i64_be` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_i64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_i64_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i64_be, io.ParseBuf.eat_i64_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_i64_be`: total; with at least 8 bytes, the 8-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.val) = some (toSigned 64 (beNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i64_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian unsigned integer. Panics on fewer (`eat_u128_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_u128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_le buf ⦃ x rest =>
      x.val = leNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄ := by
  unfold io.ParseBuf.eat_u128_le
  simp only [io.ParseBuf.eat_u128_le.SIZE]
  step*
  pb_finish

/-- `eat_u128_le` panics on a buffer of fewer than 16 bytes. -/
theorem io.ParseBuf.eat_u128_le_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    ¬ io.ParseBuf.eat_u128_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u128_le, io.ParseBuf.eat_u128_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (16 ≤ buf.length) by omega]

/-- `checked_eat_u128_le`: total; with at least 16 bytes, the 16-byte little-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u128_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i128_le`: consumes 16 bytes from the head of the buffer and returns the 16-byte little-endian two's-complement integer. Panics on fewer (`eat_i128_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_i128_le_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_le buf ⦃ x rest =>
      x.val = toSigned 128 (leNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  unfold io.ParseBuf.eat_i128_le
  simp only [io.ParseBuf.eat_i128_le.SIZE]
  step*
  pb_finish

/-- `eat_i128_le` panics on a buffer of fewer than 16 bytes. -/
theorem io.ParseBuf.eat_i128_le_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    ¬ io.ParseBuf.eat_i128_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i128_le, io.ParseBuf.eat_i128_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (16 ≤ buf.length) by omega]

/-- `checked_eat_i128_le`: total; with at least 16 bytes, the 16-byte little-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i128_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_le buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (leNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i128_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_u128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian unsigned integer. Panics on fewer (`eat_u128_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_u128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_u128_be buf ⦃ x rest =>
      x.val = beNat (buf.val.take 16) ∧ rest.val = buf.val.drop 16 ⦄ := by
  unfold io.ParseBuf.eat_u128_be
  simp only [io.ParseBuf.eat_u128_be.SIZE]
  step*
  pb_finish

/-- `eat_u128_be` panics on a buffer of fewer than 16 bytes. -/
theorem io.ParseBuf.eat_u128_be_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    ¬ io.ParseBuf.eat_u128_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_u128_be, io.ParseBuf.eat_u128_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (16 ≤ buf.length) by omega]

/-- `checked_eat_u128_be`: total; with at least 16 bytes, the 16-byte big-endian unsigned integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_u128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_u128_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_i128_be`: consumes 16 bytes from the head of the buffer and returns the 16-byte big-endian two's-complement integer. Panics on fewer (`eat_i128_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_i128_be_spec (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.eat_i128_be buf ⦃ x rest =>
      x.val = toSigned 128 (beNat (buf.val.take 16)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  unfold io.ParseBuf.eat_i128_be
  simp only [io.ParseBuf.eat_i128_be.SIZE]
  step*
  pb_finish

/-- `eat_i128_be` panics on a buffer of fewer than 16 bytes. -/
theorem io.ParseBuf.eat_i128_be_panics (buf : io.ParseBuf) (h : buf.length < 16) :
    ¬ io.ParseBuf.eat_i128_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_i128_be, io.ParseBuf.eat_i128_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (16 ≤ buf.length) by omega]

/-- `checked_eat_i128_be`: total; with at least 16 bytes, the 16-byte big-endian two's-complement integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_i128_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_i128_be buf ⦃ o rest =>
      if 16 ≤ buf.length then o.map (·.val) = some (toSigned 128 (beNat (buf.val.take 16))) ∧ rest.val = buf.val.drop 16
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_i128_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_f32_le`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte little-endian integer. Panics on fewer (`eat_f32_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_f32_le_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_f32_le
  simp only [io.ParseBuf.eat_f32_le.SIZE, core.f32.F32.from_le_bytes]
  step*
  pb_finish

/-- `eat_f32_le` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_f32_le_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_f32_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_f32_le, io.ParseBuf.eat_f32_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_f32_le`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_f32_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_le buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_f32_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_f32_be`: consumes 4 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 4-byte big-endian integer. Panics on fewer (`eat_f32_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_f32_be_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.eat_f32_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  unfold io.ParseBuf.eat_f32_be
  simp only [io.ParseBuf.eat_f32_be.SIZE, core.f32.F32.from_be_bytes]
  step*
  pb_finish

/-- `eat_f32_be` panics on a buffer of fewer than 4 bytes. -/
theorem io.ParseBuf.eat_f32_be_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ io.ParseBuf.eat_f32_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_f32_be, io.ParseBuf.eat_f32_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (4 ≤ buf.length) by omega]

/-- `checked_eat_f32_be`: total; with at least 4 bytes, the float whose IEEE-754 bit pattern is the 4-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_f32_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f32_be buf ⦃ o rest =>
      if 4 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_f32_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_f64_le`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte little-endian integer. Panics on fewer (`eat_f64_le_panics`). -/
@[step]
theorem io.ParseBuf.eat_f64_le_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_le buf ⦃ x rest =>
      x.bits.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_f64_le
  simp only [io.ParseBuf.eat_f64_le.SIZE, core.f64.F64.from_le_bytes]
  step*
  pb_finish

/-- `eat_f64_le` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_f64_le_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_f64_le buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_f64_le, io.ParseBuf.eat_f64_le.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_f64_le`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte little-endian integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_f64_le_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_le buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_f64_le
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_f64_be`: consumes 8 bytes from the head of the buffer and returns the float whose IEEE-754 bit pattern is the 8-byte big-endian integer. Panics on fewer (`eat_f64_be_panics`). -/
@[step]
theorem io.ParseBuf.eat_f64_be_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.eat_f64_be buf ⦃ x rest =>
      x.bits.val = beNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold io.ParseBuf.eat_f64_be
  simp only [io.ParseBuf.eat_f64_be.SIZE, core.f64.F64.from_be_bytes]
  step*
  pb_finish

/-- `eat_f64_be` panics on a buffer of fewer than 8 bytes. -/
theorem io.ParseBuf.eat_f64_be_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ io.ParseBuf.eat_f64_be buf ⦃ _ => True ⦄ := by
  simp [io.ParseBuf.eat_f64_be, io.ParseBuf.eat_f64_be.SIZE, io.ParseBuf.eat, core.slice.Slice.split_at,
    show ¬ (8 ≤ buf.length) by omega]

/-- `checked_eat_f64_be`: total; with at least 8 bytes, the float whose IEEE-754 bit pattern is the 8-byte big-endian integer, consumed; else `None`, buffer unchanged. -/
@[step]
theorem io.ParseBuf.checked_eat_f64_be_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_f64_be buf ⦃ o rest =>
      if 8 ≤ buf.length then o.map (·.bits.val) = some (beNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_f64_be
  step*
  all_goals split_ifs <;> simp_all

/-- `eat_lenenc_int`: the length-encoded integer at the head of the buffer, as
    `checkedLenencInt` describes it (protocol decoding, plus the documented quirk that `0xFB` and
    `0xFF` give `0`). Panics exactly when `checked_eat_lenenc_int` would return `None` (this and
    `eat_lenenc_int_panics`). -/
@[step]
theorem io.ParseBuf.eat_lenenc_int_spec (buf : io.ParseBuf) (h : (checkedLenencInt buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_int buf ⦃ n rest => (some n.val, rest.val) = checkedLenencInt buf.val ⦄ := by
  unfold io.ParseBuf.eat_lenenc_int
  rcases hb : buf.val with _ | ⟨b, rest⟩
  · simp [hb, checkedLenencInt] at h
  · have hl : 1 ≤ buf.length := by simp [Slice.length, hb]
    step
    simp [hb, leNat] at x_post x_post1
    have hx : x = b := by scalar_tac
    subst hx
    rw [hb] at h
    have h0 : 0#u8 ≤ x := by scalar_tac
    rw [ite_eq_left h0]
    by_cases h250 : x ≤ 250#u8
    · rw [ite_eq_left h250]
      step*
      have : x.val < 251 := by scalar_tac
      simp [checkedLenencInt, lenencIntDecode, x_post1, i_post, this,
        show ¬(x.val = 251 ∨ x.val = 255) by omega]
    · rw [ite_eq_right h250]
      split
      all_goals simp [checkedLenencInt, lenencIntDecode, readLE, val_mk] at h
      · split_ifs at h with hlen
        · step*
          all_goals (simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length])
        · simp at h
      · split_ifs at h with hlen
        · step*
          all_goals (simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length])
        · simp at h
      · split_ifs at h with hlen
        · step*
          all_goals (simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length])
        · simp at h
      · simp [checkedLenencInt, x_post1, val_mk]
      · simp [checkedLenencInt, x_post1, val_mk]
      · exfalso
        simp only [UScalar.eq_equiv, val_mk] at *; norm_num at *
        have := x.hBounds
        scalar_tac

/-- `eat_lenenc_int` panics when `checked_eat_lenenc_int` would return `None` (empty or truncated input). -/
theorem io.ParseBuf.eat_lenenc_int_panics (buf : io.ParseBuf) (h : (checkedLenencInt buf.val).1 = none) :
    ¬ io.ParseBuf.eat_lenenc_int buf ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.eat_lenenc_int
  rcases hb : buf.val with _ | ⟨b, rest⟩
  · exact not_spec_bind_left (io.ParseBuf.eat_u8_panics buf (by simp [Slice.length, hb]))
  · have hl : 1 ≤ buf.length := by simp [Slice.length, hb]
    apply not_spec_bind (io.ParseBuf.eat_u8_spec buf hl)
    rintro ⟨x, self1⟩ ⟨x_post, x_post1⟩
    simp [hb, leNat] at x_post x_post1
    have hx : x = b := by scalar_tac
    subst hx
    rw [hb] at h
    have h0 : 0#u8 ≤ x := by scalar_tac
    change ¬ (if 0#u8 ≤ x then _ else _) ⦃ _ => True ⦄
    rw [ite_eq_left h0]
    by_cases h250 : x ≤ 250#u8
    · have : x.val < 251 := by scalar_tac
      simp [checkedLenencInt, lenencIntDecode, this, show ¬(x.val = 251 ∨ x.val = 255) by omega] at h
    · rw [ite_eq_right h250]
      split
      all_goals simp [checkedLenencInt, lenencIntDecode, readLE, val_mk] at h
      · split_ifs at h with hlen
        exact not_spec_bind_left (io.ParseBuf.eat_u16_le_panics _ (by simp [Slice.length, x_post1]; omega))
      · split_ifs at h with hlen
        exact not_spec_bind_left (io.ParseBuf.eat_u24_le_panics _ (by simp [Slice.length, x_post1]; omega))
      · split_ifs at h with hlen
        exact io.ParseBuf.eat_u64_le_panics _ (by simp [Slice.length, x_post1]; omega)
      · simp

/-- `checked_eat_lenenc_int`: total; exactly `checkedLenencInt`. In particular a truncated
    integer gives `None` **after consuming its first byte**, and `0xFB`/`0xFF` give `Some(0)`
    (crate quirk: the protocol does not define these as integers). -/
@[step]
theorem io.ParseBuf.checked_eat_lenenc_int_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencInt buf.val ⦄ := by
  unfold io.ParseBuf.checked_eat_lenenc_int
  step
  rcases h : buf.val with _ | ⟨b, rest⟩
  · simp_all [checkedLenencInt]
  · have hl : 1 ≤ buf.length := by simp [Slice.length, h]
    simp only [hl, if_true, h] at o_post
    obtain ⟨ho, hs⟩ := o_post
    cases o with
    | none => simp at ho
    | some x =>
      simp [leNat] at ho
      have hx : x = b := by scalar_tac
      subst hx
      simp only [List.drop_one, List.tail_cons] at hs
      have h0 : 0#u8 ≤ x := by scalar_tac
      dsimp only
      rw [ite_eq_left h0]
      by_cases h250 : x ≤ 250#u8
      · rw [ite_eq_left h250]
        step*
        have : x.val < 251 := by scalar_tac
        simp [checkedLenencInt, lenencIntDecode, hs, i_post, this, show ¬(x.val = 251 ∨ x.val = 255) by omega]
      · rw [ite_eq_right h250]
        split
        · step*
          all_goals (subst_vars; split_ifs at * <;> simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length] <;> rw [ite_eq_right (by omega)])
        · step*
          all_goals (subst_vars; split_ifs at * <;> simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length] <;> rw [ite_eq_right (by omega)])
        · step*
          all_goals (subst_vars; split_ifs at * <;> simp_all [checkedLenencInt, lenencIntDecode, readLE, val_mk, Slice.length] <;> rw [ite_eq_right (by omega)])
        · simp [checkedLenencInt, hs, val_mk]
        · simp [checkedLenencInt, hs, val_mk]
        · exfalso
          simp only [UScalar.eq_equiv, val_mk, BitVec.toNat_ofNat] at *; norm_num at *
          have := x.hBounds
          scalar_tac

/-- Round trip: `checked_eat_lenenc_int` reads back `lenencInt n`, for every `n : u64`. -/
theorem io.ParseBuf.checked_eat_lenenc_int_roundtrip (n : U64) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencInt n.val ++ tail) :
    io.ParseBuf.checked_eat_lenenc_int buf ⦃ o rest => o = some n ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (io.ParseBuf.checked_eat_lenenc_int_spec buf)
  rintro ⟨o, rest⟩ ho
  simp only [WP.uncurry'_pair] at ho ⊢
  rw [h, checkedLenencInt_lenencInt n.val tail (by scalar_tac)] at ho
  simp only [Prod.mk.injEq] at ho
  obtain ⟨h1, h2⟩ := ho
  refine ⟨?_, h2⟩
  cases o with
  | none => simp at h1
  | some x => simp at h1; simp [UScalar.eq_equiv, h1]

/-- `eat_lenenc_str`: the length-encoded string at the head of the buffer (`checkedLenencStr`).
    Panics exactly when `checked_eat_lenenc_str` would return `None` (this and
    `eat_lenenc_str_panics`). (Its doc says a malformed
    length starting with `0xFF` gives an empty slice: that is the `0xFF`-is-`0` quirk, which applies
    to `0xFB` too.) -/
theorem io.ParseBuf.eat_lenenc_str_spec (buf : io.ParseBuf) (h : (checkedLenencStr buf.val).1.isSome) :
    io.ParseBuf.eat_lenenc_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenencStr buf.val ⦄ := by
  unfold io.ParseBuf.eat_lenenc_str
  have hs : (checkedLenencInt buf.val).1.isSome := by
    simp only [checkedLenencStr] at h; split at h <;> simp_all
  simp only [checkedLenencStr] at h ⊢
  step*
  all_goals (
    rw [← len_post] at h
    try rw [← len_post]
    simp only [] at h ⊢
    split_ifs at h with hle <;> try simp at h
    have hb : (↑self1 : List U8).length < 2 ^ UScalarTy.Usize.numBits := by
      have := self1.property; simp [Usize.max] at this ⊢; scalar_tac
    have hi : i.val = len.val := by
      rw [i_post]; exact UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by omega)
    first | (simp only [Slice.length, hi]; omega) | simp_all)

/-- `eat_lenenc_str` panics when `checked_eat_lenenc_str` would return `None`. (Needs the 64-bit
    target: on a 32-bit `usize` a length `≥ 2^32` is truncated by `len as usize` and may fit.) -/
theorem io.ParseBuf.eat_lenenc_str_panics (h64 : Target64) (buf : io.ParseBuf) (h : (checkedLenencStr buf.val).1 = none) :
    ¬ io.ParseBuf.eat_lenenc_str buf ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.eat_lenenc_str
  simp only [checkedLenencStr] at h
  rcases hc : checkedLenencInt buf.val with ⟨_ | n, rest⟩
  · exact not_spec_bind_left (io.ParseBuf.eat_lenenc_int_panics buf (by simp [hc]))
  · rw [hc] at h
    simp at h
    apply not_spec_bind (io.ParseBuf.eat_lenenc_int_spec buf (by simp [hc]))
    rintro ⟨len, self1⟩ hpost
    rw [hc] at hpost
    simp at hpost
    simp only [lift, bind_ok]
    apply eat_fail
    rw [cast_usize_64 h64]
    obtain ⟨h1, h2⟩ := hpost
    simp only [Slice.length, h1, h2]
    split_ifs at h with hle <;> first | omega | simp at h

/-- `checked_eat_lenenc_str`: total; exactly `checkedLenencStr`: `None` after consuming the
    length's first byte if the length is truncated, `None` after consuming the whole length if the
    bytes are missing. (Needs the 64-bit target: on a 32-bit `usize` a length `≥ 2^32` would be
    truncated by `len as usize`.) -/
theorem io.ParseBuf.checked_eat_lenenc_str_spec (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenencStr buf.val ⦄ := by
  unfold io.ParseBuf.checked_eat_lenenc_str
  apply WP.spec_bind (io.ParseBuf.checked_eat_lenenc_int_spec buf)
  rintro ⟨o, self1⟩ ho
  simp only [WP.uncurry'_pair] at ho
  simp only [checkedLenencStr, ← ho]
  cases o with
  | none => simp
  | some x =>
    simp only [lift, bind_ok, Option.map_some]
    apply WP.spec_mono (checked_eat_ok self1 _)
    rintro ⟨o', rest⟩ h'
    rw [cast_usize_64 h64] at h'
    simp only [WP.uncurry'_pair] at h' ⊢
    split_ifs at h' ⊢ <;> simp_all

/-- Round trip: `checked_eat_lenenc_str` reads back `lenencStr s`. -/
theorem io.ParseBuf.checked_eat_lenenc_str_roundtrip (s : List U8) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = lenencStr s ++ tail) :
    io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest => o.map (·.val) = some s ∧ rest.val = tail ⦄ := by
  have hb : buf.val.length < 2 ^ UScalarTy.Usize.numBits := by
    have := buf.property; simp [Usize.max] at this ⊢; scalar_tac
  have hsl : s.length < 2 ^ UScalarTy.Usize.numBits := by
    have : s.length ≤ buf.val.length := by simp [h, lenencStr]; omega
    omega
  have hs64 : s.length < 2 ^ 64 := by
    have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by
      simp only [UScalarTy.Usize_numBits_eq]; cases System.Platform.numBits_eq <;> omega)
    omega
  unfold io.ParseBuf.checked_eat_lenenc_str
  apply WP.spec_bind (io.ParseBuf.checked_eat_lenenc_int_spec buf)
  rintro ⟨o, self1⟩ ho
  simp only [WP.uncurry'_pair] at ho
  rw [h, lenencStr, List.append_assoc, checkedLenencInt_lenencInt _ _ hs64] at ho
  simp only [Prod.mk.injEq] at ho
  obtain ⟨h1, h2⟩ := ho
  cases o with
  | none => simp at h1
  | some x =>
    simp at h1
    simp only [lift, bind_ok]
    have hi : (UScalar.cast .Usize x).val = s.length := by
      rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by omega), h1]
    apply WP.spec_mono (checked_eat_ok self1 _)
    rintro ⟨o', rest⟩ h'
    simp only [WP.uncurry'_pair, hi, Slice.length, h2] at h' ⊢
    simp at h'
    simp_all

/-- `eat_u8_str`: a string with a `u8` length prefix. Panics exactly when `checked_eat_u8_str` returns `None` (this and `eat_u8_str_panics`). -/
theorem io.ParseBuf.eat_u8_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 1 buf.val).1.isSome) :
    io.ParseBuf.eat_u8_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  unfold io.ParseBuf.eat_u8_str
  simp only [checkedLenPrefixed, readLE] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · step*
    all_goals (simp_all; try (split_ifs at h <;> simp_all))
  all_goals simp_all

/-- `eat_u8_str` panics when `checked_eat_u8_str` returns `None`. -/
theorem io.ParseBuf.eat_u8_str_panics (buf : io.ParseBuf) (h : (checkedLenPrefixed 1 buf.val).1 = none) :
    ¬ io.ParseBuf.eat_u8_str buf ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.eat_u8_str
  simp only [checkedLenPrefixed, readLE] at h
  split_ifs at h with h1 h2
  · apply not_spec_bind (io.ParseBuf.eat_u8_spec buf h1)
    rintro ⟨x, self1⟩ ⟨hx, hs⟩
    simp only [lift, bind_ok]
    apply eat_fail
    simp_all [Slice.length]
    split_ifs at h <;> simp_all
  · exact not_spec_bind_left (io.ParseBuf.eat_u8_panics buf (by simp only [Slice.length]; omega))

/-- `checked_eat_u8_str`: total; `checkedLenPrefixed 1` (a missing body gives `None` after consuming the length byte). -/
theorem io.ParseBuf.checked_eat_u8_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u8_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  unfold io.ParseBuf.checked_eat_u8_str
  step*
  all_goals (simp only [checkedLenPrefixed, readLE]; split_ifs at * <;> simp_all)

/-- `eat_u32_str`: a string with a little-endian `u32` length prefix. Panics exactly when `checked_eat_u32_str` returns `None` (this and `eat_u32_str_panics`). -/
theorem io.ParseBuf.eat_u32_str_spec (buf : io.ParseBuf) (h : (checkedLenPrefixed 4 buf.val).1.isSome) :
    io.ParseBuf.eat_u32_str buf ⦃ s rest => (some s.val, rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  unfold io.ParseBuf.eat_u32_str
  simp only [checkedLenPrefixed, readLE] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · step*
    all_goals (simp_all; try (split_ifs at h <;> simp_all))
  all_goals simp_all

/-- `eat_u32_str` panics when `checked_eat_u32_str` returns `None`. -/
theorem io.ParseBuf.eat_u32_str_panics (buf : io.ParseBuf) (h : (checkedLenPrefixed 4 buf.val).1 = none) :
    ¬ io.ParseBuf.eat_u32_str buf ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.eat_u32_str
  simp only [checkedLenPrefixed, readLE] at h
  split_ifs at h with h1 h2
  · apply not_spec_bind (io.ParseBuf.eat_u32_le_spec buf h1)
    rintro ⟨x, self1⟩ ⟨hx, hs⟩
    simp only [lift, bind_ok]
    apply eat_fail
    simp_all [Slice.length]
    split_ifs at h <;> simp_all
  · exact not_spec_bind_left (io.ParseBuf.eat_u32_le_panics buf (by simp only [Slice.length]; omega))

/-- `checked_eat_u32_str`: total; `checkedLenPrefixed 4` (a missing body gives `None` after consuming the 4 length bytes). -/
theorem io.ParseBuf.checked_eat_u32_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.checked_eat_u32_str buf ⦃ o rest =>
      (o.map (·.val), rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  unfold io.ParseBuf.checked_eat_u32_str
  step*
  all_goals (simp only [checkedLenPrefixed, readLE]; split_ifs at * <;> simp_all)

/-- `eat_null_str`: total; the bytes before the first `0`, consuming the `0` too; if there is no
    `0`, the whole buffer (documented). -/
theorem io.ParseBuf.eat_null_str_spec (buf : io.ParseBuf) :
    io.ParseBuf.eat_null_str buf ⦃ s rest =>
      s.val = beforeZero buf.val ∧ rest.val = buf.val.drop ((beforeZero buf.val).length + 1) ⦄ := by
  unfold io.ParseBuf.eat_null_str
  step
  cases o with
  | none =>
    simp only at o_post
    have hbz := beforeZero_of_all _ o_post
    step*
    all_goals
      have hpos : pos.val = buf.val.length := by simp [pos_post, Slice.length]
      have hx : x.val = buf.val := by rw [x_post, hpos, List.take_length]
      have hs1 : self1.val = [] := by rw [x_post1, hpos, List.drop_length]
    · exfalso
      have hm : i1 ∈ x.val := by rw [i1_post]; exact List.getElem_mem _
      rw [hx] at hm
      apply o_post i1 hm
      have h0 : i1 = 0#u8 := by assumption
      rw [h0]; rfl
    · exact ⟨by rw [hx, hbz], by rw [hs1, hbz, List.drop_eq_nil_of_le (by omega)]⟩
    · exact ⟨by rw [hx, hbz], by rw [hs1, hbz, List.drop_eq_nil_of_le (by omega)]⟩
  | some p =>
    simp only at o_post
    obtain ⟨hp, hall, h0⟩ := o_post
    have hp' : p.val < buf.val.length := by simpa [Slice.length] using hp
    have hbz := beforeZero_of_zero _ _ hp' hall h0
    have hlbz : (beforeZero buf.val).length = p.val := by rw [hbz]; simp; omega
    step*
    all_goals
      have hx : x.val = buf.val.take (p.val + 1) := by rw [x_post, pos_post]
      have hxl : x.val.length = p.val + 1 := by rw [hx]; simp; omega
      have hs1 : self1.val = buf.val.drop (p.val + 1) := by rw [x_post1, pos_post]
    · refine ⟨?_, by rw [hs1, hlbz]⟩
      have hi : i.val = p.val := by scalar_tac
      rw [x1_post, List.slice_zero_j, hi, hx, List.take_take, hbz]
      congr 1; omega
    · exfalso
      have hi : i.val = p.val := by scalar_tac
      have : i1 = buf.val[p.val]! := by
        rw [i1_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hp']
        simp [hx, hi]
      apply ‹¬i1 = 0#u8›
      rw [UScalar.eq_equiv, this, h0]; rfl

end mysql_common
