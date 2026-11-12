import Proofs.Value.Convert.Time.ParseIrPlainDateTime
import Proofs.Value.Convert.Time.ParseIrDate
import Proofs.Value.Convert.Time.ParseIrTime
import Proofs.Value.Convert.Time.ParseIrSignedDuration
import Proofs.Value.Convert.Time.FromParseIr
import Proofs.Value.Convert.Time.FromPlainDateTime
import Proofs.Value.Convert.Time.FromDate
import Proofs.Value.Convert.Time.FromTime
import Proofs.Value.Convert.Time.FromSignedDuration

/-!
# `src/value/convert/time.rs`
    `FromValue` and `From<_> for Value` for the `time` crate's `PrimitiveDateTime`, `Date`, `Time`
    and `Duration`. time's types are opaque; the statements speak about them through their
    getters (`timeDate`, `timeTime`, `timeDateTime`). time's own text parsers and its `Duration`
    arithmetic are opaque with no specification: there the statements are glue-level (which
    opaque parser is called on what; the result is whatever it returns; on failure the original
    value is returned).

    **Configuration.** As in `Specs/Io.lean` (feature `time`, time 0.3.55 without `large-dates`).

    **Definitions used.** `Defs/Convert.lean` (`timeDate`, `timeTime`, `timeDateTime`,
    `timeDateValid`, `timeTimeValid`, `Val.bytesAscii`, `timeStringRead`, `IsUtf8`),
    `Trusted.daysInMonth`, `Trusted.monthNumber`, `Defs/Value.lean`, `Defs/Bytes.lean`.

    **Trusted axioms these statements rest on** (`FunsExternal.lean`, namespace `Trusted`):
    `Date.ofCalendarDate`, `Date.year`/`month`/`day`, `Date.ofCalendarDate_isSome`,
    `Date.ofCalendarDate_some`, `timeFromHmsMicro`, `timeFromHmsMicro_spec`,
    `Time.hour`/`minute`/`second`/`microsecond`, `PrimitiveDateTime.new`/`date`/`time`,
    `PrimitiveDateTime.date_new`, `PrimitiveDateTime.time_new`; the opaque parsers
    `dateParseDate`, `timeParseTime`, `timeParseTimeMicro`, `pdtParseDate`, `pdtParseDateTime`,
    `pdtParseDateTimeMicro`; the opaque `time::Duration` operations `durationDays`,
    `durationHours`, `durationMinutes`, `durationSeconds`, `durationMicroseconds`, `durationAdd`,
    `durationSub`, `durationNeg`, `durationLtZero`, `durationWhole*`; and `isMatch`/`isMatch_ascii`
    (for `time::Duration` from `Bytes`). (`time_month_from_u8`, `time_month_to_u8` and the
    `InsufficientInformation` error are exact definitions.)

    **Behaviour to note.**
    * `From<PrimitiveDateTime>`/`From<Date> for Value` convert the year with `as u16`: a negative
      year (time allows down to -9999) wraps (e.g. -1 becomes 65535), so it does not round-trip.
    * `PrimitiveDateTime` from a 10–18 byte string parses it with the **date-only** format
      (`DATE_FORMAT`), which cannot produce a `PrimitiveDateTime` (no hour): a text `DATE` such as
      `"2024-01-31"` is probably always rejected, while `Value::Date` with zero time is accepted.
      (Not provable here: time's parsers are opaque.)
    * `time::Duration` conversions use time's arithmetic, which is not assumed not to panic: only
      "if it returns" statements are made about them.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl TryFrom<Value> for ParseIr<PrimitiveDateTime>` -/

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on a `Date`: total; converts exactly when
    time accepts the date and the time, to the date-time with these fields. -/
recall value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧
        timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date`

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on `Bytes`: not valid UTF-8 is an error;
    otherwise time's parser (opaque) with the format chosen by the length — more than 19 bytes:
    date-time with fraction; 19: date-time; 10 to 18: date only; fewer: an error. -/
recall value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if 19 < b.val.length then Trusted.pdtParseDateTimeMicro (alloc.vec.Vec.deref b)
          else if b.val.length = 19 then Trusted.pdtParseDateTime (alloc.vec.Vec.deref b)
          else if 10 ≤ b.val.length then Trusted.pdtParseDate (alloc.vec.Vec.deref b)
          else .Err (.TryFromParsed .InsufficientInformation)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes`

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>`: any other value is an error. -/
recall value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other`

/-! ### `impl TryFrom<Value> for ParseIr<Date>` -/

/-- `TryFrom<Value> for ParseIr<Date>` on a `Date`: total; only the date fields are read;
    converts exactly when time accepts them. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧ timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date`

/-- `TryFrom<Value> for ParseIr<Date>` on `Bytes`: time's date parser (opaque) on valid UTF-8. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, .Bytes b)
        | none => .Err (.Bytes b)
      else .Err (.Bytes b))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes`

/-- `TryFrom<Value> for ParseIr<Date>`: any other value is an error. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other`

/-! ### `impl TryFrom<Value> for ParseIr<Time>` -/

/-- `TryFrom<Value> for ParseIr<Time>` on a positive `TIME` with 0 days: total; converts exactly
    when time accepts the fields. -/
recall value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time (h m s : U8) (us : U32) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Time false 0#u32 h m s us ∧ timeTime x = (h.val, m.val, s.val, us.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time`

/-- `TryFrom<Value> for ParseIr<Time>` on `Bytes`: not valid UTF-8 or fewer than 8 bytes is an
    error; 8 bytes: time's `hh:mm:ss` parser; more: the parser with a fraction (both opaque). -/
recall value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if b.val.length < 8 then .Err (.TryFromParsed .InsufficientInformation)
          else if b.val.length = 8 then Trusted.timeParseTime (alloc.vec.Vec.deref b)
          else Trusted.timeParseTimeMicro (alloc.vec.Vec.deref b)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes`

/-- `TryFrom<Value> for ParseIr<Time>`: any other value (including a negative `TIME` or one with
    days) is an error. -/
recall value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other`

/-! ### `impl TryFrom<Value> for ParseIr<time::Duration>` -/

/-- `TryFrom<Value> for ParseIr<time::Duration>` (glue level: time's `Duration` arithmetic is
    opaque and may panic): on a `TIME`, or on `Bytes` (ASCII) holding a text `TIME` literal, if it
    returns, it returns `Ok` keeping the original value; on other `Bytes` or any other value it
    is an error carrying the value. -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) (r : core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration) value.convert.FromValueError)
    (h : value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok r) :
    match Val.ofValue v with
    | .time .. => ∃ x, r = .Ok (x, v)
    | .bytes b => (timeStringRead b).isSome → ∃ x, r = .Ok (x, v)
    | _ => r = .Err v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `TryFrom<Value> for ParseIr<time::Duration>` is an error (no opaque call) on `Bytes` (ASCII)
    that are not a text `TIME` literal and on every value other than `TIME` and `Bytes`. -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err`

/-! ### `impl From<ParseIr<_>> for PrimitiveDateTime, Date, Time, time::Duration and for Value` -/

/-- `From<ParseIr<PrimitiveDateTime>>` for `PrimitiveDateTime` is `commit`, for `Value` is
    `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from_eq (x : time.plain_date_time.PlainDateTime) (w : value.Value) :
    time.plain_date_time.PlainDateTime.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from_eq`

/-- `From<ParseIr<Date>>` for `Date` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrDate.from_eq (x : time.date.Date) (w : value.Value) :
    time.date.Date.Insts.CoreConvertFromParseIrDate.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDate.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrDate.from_eq`

/-- `From<ParseIr<Time>>` for `Time` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrTime.from_eq (x : time.time.Time) (w : value.Value) :
    time.time.Time.Insts.CoreConvertFromParseIrTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrTime.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrTime.from_eq`

/-- `From<ParseIr<time::Duration>>` for `time::Duration` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrSignedDuration.from_eq (x : time.signed_duration.SignedDuration) (w : value.Value) :
    time.signed_duration.SignedDuration.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrSignedDuration.from_eq`

/-! ### `impl From<PrimitiveDateTime> for Value` -/

/-- `From<PrimitiveDateTime> for Value`: total; the `Date` of its fields (the year `as u16`, so
    taken mod `2^16`). -/
recall value.Value.Insts.CoreConvertFromPlainDateTime.from_spec (x : time.plain_date_time.PlainDateTime) :
    value.Value.Insts.CoreConvertFromPlainDateTime.from x ⦃ w =>
      Val.ofValue w = match timeDateTime x with
        | ((y, mo, d), (h, mi, s, us)) => .date (y % 2 ^ 16).toNat mo d h mi s us ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromPlainDateTime.from_spec`

/-- Round trip: a valid date-time with a year in `[0, 9999]` reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip (x : time.plain_date_time.PlainDateTime)
    (hv : match timeDateTime x with
      | ((y, mo, d), (h, mi, s, us)) => 0 ≤ y ∧ timeDateValid y mo d ∧ timeTimeValid h mi s us) :
    (do let w ← value.Value.Insts.CoreConvertFromPlainDateTime.from x; value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDateTime x' = timeDateTime x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip`

/-! ### `impl From<Date> for Value` -/

/-- `From<Date> for Value`: total; the `Date` with zero time (the year taken mod `2^16`). -/
recall value.Value.Insts.CoreConvertFromDate.from_spec (x : time.date.Date) :
    value.Value.Insts.CoreConvertFromDate.from x ⦃ w =>
      Val.ofValue w = match timeDate x with | (y, mo, d) => .date (y % 2 ^ 16).toNat mo d 0 0 0 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDate.from_spec`

/-- Round trip: a valid date with a year in `[0, 9999]` reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromDate.roundtrip (x : time.date.Date) (hv : match timeDate x with | (y, mo, d) => 0 ≤ y ∧ timeDateValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromDate.from x; value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDate x' = timeDate x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDate.roundtrip`

/-! ### `impl From<Time> for Value` -/

/-- `From<Time> for Value`: total; the positive `TIME` with 0 days of its fields. -/
recall value.Value.Insts.CoreConvertFromTime.from_spec (x : time.time.Time) :
    value.Value.Insts.CoreConvertFromTime.from x ⦃ w =>
      Val.ofValue w = match timeTime x with | (h, m, s, us) => .time false 0 h m s us ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromTime.from_spec`

/-- Round trip: a valid time reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromTime.roundtrip (x : time.time.Time) (hv : match timeTime x with | (h, m, s, us) => timeTimeValid h m s us) :
    (do let w ← value.Value.Insts.CoreConvertFromTime.from x; value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeTime x' = timeTime x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromTime.roundtrip`

/-! ### `impl From<time::Duration> for Value` -/

/-- `From<time::Duration> for Value` (glue level: time's `Duration` arithmetic is opaque and may
    panic): if it returns, it is a `TIME` whose sign is whether the duration is negative. -/
recall value.Value.Insts.CoreConvertFromSignedDuration.from_sign (x : time.signed_duration.SignedDuration) (w : value.Value) (h : value.Value.Insts.CoreConvertFromSignedDuration.from x = ok w) :
    ∃ d hh m s us, w = .Time (Trusted.durationLtZero x) d hh m s us

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.from_sign`

end mysql_common
