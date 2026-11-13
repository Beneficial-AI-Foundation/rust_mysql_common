import Proofs.Binlog.Misc.TIMEF_INT_OFS
import Proofs.Binlog.Misc.TIMEF_OFS
import Proofs.Binlog.Misc.DATETIMEF_INT_OFS
import Proofs.Binlog.Misc.MyPackedTimeMakeInt
import Proofs.Binlog.Misc.MyPackedTimeMake
import Proofs.Binlog.Misc.MyTimePackedFromBinary
import Proofs.Binlog.Misc.MyPackedTimeGetIntPart
import Proofs.Binlog.Misc.MyPackedTimeGetFracPart
import Proofs.Binlog.Misc.TimeFromPacked
import Proofs.Binlog.Misc.MyDatetimePackedFromBinary
import Proofs.Binlog.Misc.DatetimeFromPacked
import Proofs.Binlog.Misc.MyTimestampFromBinary

/-!
# `src/binlog/misc.rs`
    The packed temporal helpers: the TIME2 / DATETIME2 / TIMESTAMP2 binary readers and the packed
    value accessors, against MySQL's `mysys/my_time.cc` (`Defs/BinlogCore.lean`), with round trips
    against MySQL's writers (`my_*_to_binary`).

    **Patch.** Patch 149 replaces the `byteorder::ReadBytesExt` calls on `&mut ParseBuf` by
    private readers (`read_u8`, `read_u24_be`, ...) on `ParseBuf`'s checked readers, with
    `read_exact`'s failure behaviour: on a short input the reader consumes what is left and fails
    (`read_eof`). So every error of these functions leaves the buffer **empty**.

    **Configuration.** As in `Specs/Binlog/Mod.lean`.

    Panics are stated as equations `f x = fail e` (see `Specs/Value.lean`); overflow is
    `.integerOverflow` (debug semantics, see `lean/README.md`).

    **Definitions used.** `Defs/BinlogCore.lean` (`packedIntPart`, `packedFracPart`,
    `packedMake`, `wrapI64`, `fracUnit`, `time2Read`, `time2Bin`, `time2NegFracBug`,
    `timeFromPacked`, `datetime2Read`, `datetime2Bin`, `datetimeFromPacked`, `timestamp2Read`,
    `timestamp2Bin`), `Defs/Value.lean` (`Val`), `Defs/Bytes.lean`.

    **Trusted axioms.** `binlog.trusted.read_exact_eof` (opaque: the `io::Error` value; nothing is
    assumed about it, and the statements say nothing about errors beyond `okPart r = none`).

    **Not covered.** The private `read_*` helpers (covered through the public readers);
    `LimitedWrite`/`LimitWrite` (used only by `Event::write`, out of scope).

    **Behaviour to note.**
    * **Bug** (`my_time_packed_from_binary`, 1–2 fractional digits): MySQL's `frac -= 0x100` is
      computed in `u32`, so every negative TIME(1)/TIME(2) value with a non-zero fraction (e.g.
      `-00:00:00.5`) panics in debug builds (`my_time_packed_from_binary_neg_frac`); in release
      builds it wraps and gives a wrong value. A server can therefore crash the client.
    * `my_datetime_packed_from_binary` overflows `i64` (panics) on the invalid DATETIME2 integer
      part 0 with a negative fraction; `time_from_packed`/`datetime_from_packed` panic on
      `i64::MIN` (negation), which `my_datetime_packed_from_binary` returns for an integer part 0
      without fraction.
    * `datetime_from_packed` drops the sign MySQL records (DATETIMEs are never negative).
    * `my_timestamp_from_binary` reads the seconds as `i32` and a 1–2-digit fraction byte as
      signed, where MySQL reads both unsigned; they differ only on data MySQL never writes
      (seconds from 2^31, fraction bytes from 128).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `const TIMEF_INT_OFS` -/

/-- `TIMEF_INT_OFS` = `0x800000` (MySQL's). -/
recall binlog.misc.TIMEF_INT_OFS_val :
    binlog.misc.TIMEF_INT_OFS.val = 0x800000

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.TIMEF_INT_OFS_val`
/-! ### `const TIMEF_OFS` -/

/-- `TIMEF_OFS` = `0x800000000000` (MySQL's). -/
recall binlog.misc.TIMEF_OFS_val :
    binlog.misc.TIMEF_OFS.val = 0x800000000000

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.TIMEF_OFS_val`
/-! ### `const DATETIMEF_INT_OFS` -/

/-- `DATETIMEF_INT_OFS` = `0x8000000000` (MySQL's). -/
recall binlog.misc.DATETIMEF_INT_OFS_val :
    binlog.misc.DATETIMEF_INT_OFS.val = 0x8000000000

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.DATETIMEF_INT_OFS_val`
/-! ### `fn my_packed_time_make_int` -/

/-- `my_packed_time_make_int(i)`: total; `MY_PACKED_TIME_MAKE_INT(i)` = `(i as u64) << 24`, reinterpreted as `i64` (wraps; exact, `packedMake i 0`, for `|i| < 2^39`). -/
recall binlog.misc.my_packed_time_make_int_spec (i : I64) :
    binlog.misc.my_packed_time_make_int i ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_packed_time_make_int_spec`
/-! ### `fn my_packed_time_make` -/

/-- `my_packed_time_make(i, f)`: `MY_PACKED_TIME_MAKE(i, f)`: `my_packed_time_make_int(i) + f`, when the sum fits in `i64`. -/
recall binlog.misc.my_packed_time_make_spec (i f : I64)
    (h : -2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63) :
    binlog.misc.my_packed_time_make i f ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) + f.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_packed_time_make_spec`
/-- `my_packed_time_make(i, f)` panics (`i64` overflow of the addition) otherwise. -/
recall binlog.misc.my_packed_time_make_overflow (i f : I64)
    (h : ¬(-2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63)) :
    binlog.misc.my_packed_time_make i f = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_packed_time_make_overflow`
/-! ### `fn my_time_packed_from_binary` -/

/-- `my_time_packed_from_binary(input, dec)`: exact on any input outside the bug below: MySQL's packed TIME2 value (`time2Read`) and the rest of the input, or an error with the input emptied when it is shorter than `3 + fracBytes dec` bytes. -/
recall binlog.misc.my_time_packed_from_binary_spec (input : io.ParseBuf) (dec : U32)
    (hbug : ¬ time2NegFracBug dec.val input.val) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) =
        (match time2Read dec.val input.val with
         | some (p, t) => (some p, t)
         | none => (none, [])) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_time_packed_from_binary_spec`
/-- **Bug (crash path).** With 1 or 2 fractional digits, a negative integer part and a non-zero fraction byte (`time2NegFracBug`: every negative TIME(1)/TIME(2) value with a fraction, see `Defs.time2NegFracBug_time2Bin`), the crate computes MySQL's `frac -= 0x100` in `u32` (MySQL: `int`) and panics (underflow; in release builds it wraps and returns a wrong value). -/
recall binlog.misc.my_time_packed_from_binary_neg_frac (input : io.ParseBuf) (dec : U32)
    (h : time2NegFracBug dec.val input.val) :
    binlog.misc.my_time_packed_from_binary input dec = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_time_packed_from_binary_neg_frac`
/-- Round trip: `my_time_packed_from_binary` reads back MySQL's encoding (`my_time_packed_to_binary`, `time2Bin`) of every packed TIME value in range (integer part in 23 bits plus sign, fraction a multiple of the unit of `dec` and below `10^6`), except the bug's: negative values with a fraction at 1–2 digits. -/
recall binlog.misc.my_time_packed_from_binary_roundtrip (dec : U32) (p : Int)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6)
    (hbug : ¬((dec.val = 1 ∨ dec.val = 2) ∧ p < 0 ∧ packedFracPart p ≠ 0))
    (tail : List U8) (input : io.ParseBuf) (h : input.val = time2Bin dec.val p ++ tail) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_time_packed_from_binary_roundtrip`
/-! ### `fn my_packed_time_get_int_part` -/

/-- `my_packed_time_get_int_part(i)`: total; `i >> 24` (arithmetic). -/
recall binlog.misc.my_packed_time_get_int_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_int_part i ⦃ r => r.val = packedIntPart i.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_packed_time_get_int_part_spec`
/-! ### `fn my_packed_time_get_frac_part` -/

/-- `my_packed_time_get_frac_part(i)`: total; `i % 2^24` with the sign of `i` (C's and Rust's `%`). -/
recall binlog.misc.my_packed_time_get_frac_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_frac_part i ⦃ r => r.val = packedFracPart i.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_packed_time_get_frac_part_spec`
/-! ### `fn time_from_packed` -/

/-- `time_from_packed(tmp)`: MySQL's `TIME_from_longlong_time_packed` (`timeFromPacked`: sign, hours from 10 bits split into days and hours, minutes, seconds, microseconds), for every `tmp` but `i64::MIN`. -/
recall binlog.misc.time_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.time_from_packed tmp ⦃ v => Val.ofValue v = timeFromPacked tmp.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.time_from_packed_spec`
/-- `time_from_packed(i64::MIN)` panics (negation overflow; no TIME2 encoding gives it). -/
recall binlog.misc.time_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.time_from_packed tmp = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.time_from_packed_min`
/-! ### `fn my_datetime_packed_from_binary` -/

/-- `my_datetime_packed_from_binary(input, dec)`: exact when the packed value fits in `i64`: MySQL's packed DATETIME2 value (`datetime2Read`) and the rest, or an error with the input emptied when it is shorter than `5 + fracBytes dec` bytes. -/
recall binlog.misc.my_datetime_packed_from_binary_spec (input : io.ParseBuf) (dec : U32)
    (h : ∀ p t, datetime2Read dec.val input.val = some (p, t) → -2 ^ 63 ≤ p) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) =
        (match datetime2Read dec.val input.val with
         | some (p, t) => (some p, t)
         | none => (none, [])) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_datetime_packed_from_binary_spec`
/-- `my_datetime_packed_from_binary` panics (`i64` overflow) when the packed value is below `-2^63`: an integer part of five zero bytes (invalid: MySQL always sets the top bit) with a negative fraction. -/
recall binlog.misc.my_datetime_packed_from_binary_overflow (input : io.ParseBuf) (dec : U32)
    (h : ∃ p t, datetime2Read dec.val input.val = some (p, t) ∧ p < -2 ^ 63) :
    binlog.misc.my_datetime_packed_from_binary input dec = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_datetime_packed_from_binary_overflow`
/-- Round trip: `my_datetime_packed_from_binary` reads back MySQL's encoding (`my_datetime_packed_to_binary`, `datetime2Bin`) of every non-negative packed DATETIME value below `2^63` whose fraction is a multiple of the unit of `dec` and below `10^6`. -/
recall binlog.misc.my_datetime_packed_from_binary_roundtrip (dec : U32) (p : Int)
    (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ packedFracPart p < 10 ^ 6)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = datetime2Bin dec.val p ++ tail) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_datetime_packed_from_binary_roundtrip`
/-! ### `fn datetime_from_packed` -/

/-- `datetime_from_packed(tmp)`: MySQL's `TIME_from_longlong_datetime_packed` of `|tmp|` (`datetimeFromPacked`), for every `tmp` but `i64::MIN`. The sign MySQL records is dropped. -/
recall binlog.misc.datetime_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp ⦃ v => Val.ofValue v = datetimeFromPacked tmp.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.datetime_from_packed_spec`
/-- `datetime_from_packed(i64::MIN)` panics (negation overflow). `my_datetime_packed_from_binary` returns `i64::MIN` for an integer part of five zero bytes without fraction, so the invalid DATETIME2 `00 00 00 00 00` crashes `BinlogValue` decoding. -/
recall binlog.misc.datetime_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.datetime_from_packed_min`
/-! ### `fn my_timestamp_from_binary` -/

/-- `my_timestamp_from_binary(input, dec)`: total; the seconds and microseconds (`timestamp2Read`) and the rest, or an error with the input emptied when it is shorter than `4 + fracBytes dec` bytes. -/
recall binlog.misc.my_timestamp_from_binary_spec (input : io.ParseBuf) (dec : U8) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      ((okPart r).map (fun x => (x.1.val, x.2.val)), rest.val) =
        (match timestamp2Read dec.val input.val with
         | some (x, t) => (some x, t)
         | none => (none, [])) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_timestamp_from_binary_spec`
/-- Round trip: `my_timestamp_from_binary` reads back MySQL's encoding (`my_timestamp_to_binary`, `timestamp2Bin`) of every TIMESTAMP in range (seconds below `2^31`, MySQL's 2038 limit; fraction a multiple of the unit of `dec` and below `10^6`). -/
recall binlog.misc.my_timestamp_from_binary_roundtrip (dec : U8) (sec usec : Nat) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec.val = 0)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = timestamp2Bin dec.val sec usec ++ tail) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      (okPart r).map (fun x => (x.1.val, x.2.val)) = some ((sec : Int), (usec : Int)) ∧
        rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.misc.my_timestamp_from_binary_roundtrip`
end mysql_common
