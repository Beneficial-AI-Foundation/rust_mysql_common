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
    getters (`timeDate`, `timeTime`, `timeDateTime`; a `time::Duration` through its total
    nanoseconds, `Trusted.durNanos`). time's own text parsers are opaque with no specification:
    there the statements are glue-level (which opaque parser is called on what; the result is
    whatever it returns; on failure the original value is returned). The `time::Duration`
    conversions are **exact**: each `Duration` operation they use has an axiom saying when it
    returns and what the nanoseconds of its result are.

    **Configuration.** As in `Specs/Io.lean` (feature `time`, time 0.3.55 without `large-dates`).

    **Definitions used.** `Defs/Convert.lean` (`timeDate`, `timeTime`, `timeDateTime`,
    `timeDateValid`, `timeTimeValid`, `Val.timeTextPanics`, `timeStringRead`, `IsUtf8`,
    `timeNanos`, `timeSignedNanos`, `Val.signedDurationNanos`, `signedDurationTime`),
    `Trusted.daysInMonth`, `Trusted.monthNumber`, `Defs/Value.lean`, `Defs/Bytes.lean`.

    **Trusted axioms these statements rest on** (`FunsExternal.lean`, namespace `Trusted`):
    `Date.ofCalendarDate`, `Date.year`/`month`/`day`, `Date.ofCalendarDate_isSome`,
    `Date.ofCalendarDate_some`, `timeFromHmsMicro`, `timeFromHmsMicro_spec`,
    `Time.hour`/`minute`/`second`/`microsecond`, `PrimitiveDateTime.new`/`date`/`time`,
    `PrimitiveDateTime.date_new`, `PrimitiveDateTime.time_new`; the opaque parsers
    `dateParseDate`, `timeParseTime`, `timeParseTimeMicro`, `pdtParseDateTime`,
    `pdtParseDateTimeMicro` (`pdtParseDate` is an exact definition: always the
    `InsufficientInformation` error); for `time::Duration`, the getter `durNanos`, the opaque
    operations `durationDays`, `durationHours`, `durationMinutes`, `durationSeconds`,
    `durationMicroseconds`, `durationAdd`, `durationSub`, `durationNeg`, `durationLtZero`,
    `durationWholeDays`, `durationWholeHours`, `durationWholeMinutes`, `durationWholeSeconds`,
    `durationWholeMicroseconds`, and one axiom `<operation>_spec` for each (when it returns, and
    the `durNanos` of the result; each read off time 0.3.55's `signed_duration.rs` and checked by
    test); and `isMatch`/`isMatch_ascii`/`isMatch_loose` (for `time::Duration` from `Bytes`).
    (`time_month_from_u8`, `time_month_to_u8` and the `InsufficientInformation` error are exact
    definitions.)

    **Behaviour to note.**
    * `From<PrimitiveDateTime>`/`From<Date> for Value` convert the year with `as u16`: a negative
      year (time allows down to -9999) wraps (e.g. -1 becomes 65535), so it does not round-trip.
    * **Upstream bug:** `PrimitiveDateTime` from a 10–18 byte string parses it with the
      **date-only** format (`DATE_FORMAT`), which can never produce a `PrimitiveDateTime` (time
      0.3.55 needs an hour, parsed.rs:1235-1241, 1304): a text `DATE` such as `"2024-01-31"` is
      always rejected (`..._date_text_rejected`), while `Value::Date` with zero time is accepted.
    * `Value::from(x)` of a `time::Duration` **panics** iff `x` is at most `-2^63` seconds, which
      includes `time::Duration::MIN` (`checked_neg(..).expect(..)`, signed_duration.rs:1543):
      `from_panic`, `from_min_seconds_panics`. Otherwise it returns (`from_spec`), and
      `whole_days() as u32` wraps (`from_days_wrap`; e.g. `Duration::MAX` becomes
      `Time(false, 579025220, 15, 30, 7, 999999)`).
    * `time::Duration` round trips: `Duration → Value → Duration` preserves the nanoseconds iff
      the duration is a whole number of microseconds below `2^32` days (`roundtrip`);
      `Value::Time → Duration → Value` gives back the value iff its fields are normalised and it
      is not a negative zero (`roundtrip_value`).
    * Text `time::Time` (more than 8 bytes, `[subsecond digits:1+]`) accepts 7–9 fractional
      digits, beyond microseconds; the getter truncates to microseconds. Text `time::Date`
      accepts a signed year (`"+2024-01-31"`, `"-0001-01-01"`). (Facts about the opaque parsers,
      found in review; not stated.)
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

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, Trusted.PrimitiveDateTime.date, Trusted.PrimitiveDateTime.date_new, Trusted.PrimitiveDateTime.new, Trusted.PrimitiveDateTime.time, Trusted.PrimitiveDateTime.time_new, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date
/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on `Bytes`: not valid UTF-8 is an error;
    otherwise time's parser (opaque) with the format chosen by the length — more than 19 bytes:
    date-time with fraction; 19: date-time; 10 to 18: date only (which always fails, see
    `..._date_text_rejected`); fewer: an error. -/
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

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes
/-- **Upstream bug.** `TryFrom<Value> for ParseIr<PrimitiveDateTime>` rejects every 10–18 byte
    `Bytes`: a text `DATE` (`"2024-01-31"`) cannot be read as a `PrimitiveDateTime`, because the
    date-only format never yields an hour. -/
recall value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date_text_rejected (b : alloc.vec.Vec U8) (hl : 10 ≤ b.val.length ∧ b.val.length ≤ 18) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date_text_rejected
/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>`: any other value is an error. -/
recall value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other
/-- `from_value_opt`: as `try_from_date` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x, r = .Ok x → timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, Trusted.PrimitiveDateTime.date, Trusted.PrimitiveDateTime.date_new, Trusted.PrimitiveDateTime.new, Trusted.PrimitiveDateTime.time, Trusted.PrimitiveDateTime.time_new, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date
/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if 19 < b.val.length then Trusted.pdtParseDateTimeMicro (alloc.vec.Vec.deref b)
          else if b.val.length = 19 then Trusted.pdtParseDateTime (alloc.vec.Vec.deref b)
          else if 10 ≤ b.val.length then Trusted.pdtParseDate (alloc.vec.Vec.deref b)
          else .Err (.TryFromParsed .InsufficientInformation)) with
        | .Ok x => .Ok x
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_bytes
/-- `from_value_opt`: as `try_from_date_text_rejected` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date_text_rejected (b : alloc.vec.Vec U8) (hl : 10 ≤ b.val.length ∧ b.val.length ≤ 18) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Bytes b) = ok (.Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date_text_rejected
/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.Date.ofCalendarDate, Trusted.PrimitiveDateTime.new, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_other
/-! ### `impl TryFrom<Value> for ParseIr<Date>` -/

/-- `TryFrom<Value> for ParseIr<Date>` on a `Date`: total; only the date fields are read;
    converts exactly when time accepts them. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧ timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date
/-- `TryFrom<Value> for ParseIr<Date>` on `Bytes`: time's date parser (opaque) on valid UTF-8. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, .Bytes b)
        | none => .Err (.Bytes b)
      else .Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.ofCalendarDate, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes
/-- `TryFrom<Value> for ParseIr<Date>`: any other value is an error. -/
recall value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.ofCalendarDate, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other
/-- `from_value_opt`: as `try_from_date` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x, r = .Ok x → timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_date
/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err (.Bytes b)
      else .Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.ofCalendarDate, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_bytes
/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.ofCalendarDate, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_other
/-! ### `impl TryFrom<Value> for ParseIr<Time>` -/

/-- `TryFrom<Value> for ParseIr<Time>` on a non-negative (sign flag false) `TIME` with 0 days: total; converts exactly
    when time accepts the fields. -/
recall value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time (h m s : U8) (us : U32) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Time false 0#u32 h m s us ∧ timeTime x = (h.val, m.val, s.val, us.val) ⦄

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.timeParseTime, Trusted.timeParseTimeMicro, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time
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

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeParseTime, Trusted.timeParseTimeMicro, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes
/-- `TryFrom<Value> for ParseIr<Time>`: any other value (including a negative `TIME` or one with
    days) is an error. -/
recall value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeParseTime, Trusted.timeParseTimeMicro, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other
/-- `from_value_opt`: as `try_from_time` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_time (h m s : U8) (us : U32) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x, r = .Ok x → timeTime x = (h.val, m.val, s.val, us.val) ⦄

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.timeParseTime, Trusted.timeParseTimeMicro, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_time
/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if b.val.length < 8 then .Err (.TryFromParsed .InsufficientInformation)
          else if b.val.length = 8 then Trusted.timeParseTime (alloc.vec.Vec.deref b)
          else Trusted.timeParseTimeMicro (alloc.vec.Vec.deref b)) with
        | .Ok x => .Ok x
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeParseTime, Trusted.timeParseTimeMicro, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_bytes
/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeParseTime, Trusted.timeParseTimeMicro, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_other
/-! ### `impl TryFrom<Value> for ParseIr<time::Duration>` -/

/-- `TryFrom<Value> for ParseIr<time::Duration>`: **total and exact** off the text parser's
    panic (hypothesis: not `Bytes` on which it panics, `Val.timeTextPanics`, stated separately as
    `try_from_panic`; false of all ASCII `Bytes`). On a
    `TIME` (any fields: `u32` days cannot overflow a `time::Duration`), or on `Bytes` holding a
    text `TIME` literal, it is `Ok` of the duration with exactly the value's signed nanoseconds
    (`Val.signedDurationNanos`), keeping the original value; on other `Bytes` or any other value
    it is an error carrying the value. -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      match (Val.ofValue v).signedDurationNanos with
      | some n => ∃ x, r = .Ok (x, v) ∧ Trusted.durNanos x = n
      | none => r = .Err v ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationAdd, Trusted.durationAdd_spec, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationMicroseconds, Trusted.durationMicroseconds_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec
/-- `TryFrom<Value> for ParseIr<time::Duration>` is an error (no opaque call) on `Bytes` that
    are not a text `TIME` literal and on every value other than `TIME` and `Bytes`. Hypothesis:
    the value is not `Bytes` on which the text parser panics (`Val.timeTextPanics`, see
    `try_from_panic`; false of all ASCII `Bytes`). -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err
/-- **Crash path.** `TryFrom<Value> for ParseIr<time::Duration>` panics exactly on the `Bytes` on
    which the text parser panics (`Val.timeTextPanics`: a non-ASCII byte, and a fractional regex
    matches): the complement of the hypothesis of `try_from_spec`. -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = fail .panic

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic
/-- `TryFrom<Value> for ParseIr<time::Duration>` on `Bytes` with a non-ASCII byte never returns a
    duration: it panics or returns the error carrying the value. -/
recall value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = fail .panic ∨
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii
/-- `from_value_opt::<time::Duration>`: as `try_from_spec` of the intermediate, committed:
    **total and exact** (same hypothesis; the panic is `from_value_opt_panic`). `Ok` of the duration with exactly the value's signed
    nanoseconds for a `TIME` or a text `TIME` literal; otherwise the error carrying the value. -/
recall time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v ⦃ r =>
      match (Val.ofValue v).signedDurationNanos with
      | some n => ∃ x, r = .Ok x ∧ Trusted.durNanos x = n
      | none => r = .Err v ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationAdd, Trusted.durationAdd_spec, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationMicroseconds, Trusted.durationMicroseconds_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec
/-- `from_value_opt`: as `try_from_err` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_err (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = ok (.Err v)

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_err
/-- **Crash path.** `from_value_opt::<time::Duration>` panics exactly on the `Bytes` on which the
    text parser panics (`Val.timeTextPanics`): the complement of the hypothesis of
    `from_value_opt_spec`. -/
recall time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = fail .panic

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_panic
/-- `from_value_opt::<time::Duration>` on `Bytes` with a non-ASCII byte never returns a duration:
    it panics or returns the error carrying the value. -/
recall time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Bytes b) = fail .panic ∨
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Bytes b) = ok (.Err (.Bytes b))

/-- [propext, choice, Quot.sound, Trusted.durationAdd, Trusted.durationDays, Trusted.durationHours, Trusted.durationMicroseconds, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationSeconds, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_nonascii
/-! ### `impl From<ParseIr<_>> for PrimitiveDateTime, Date, Time, time::Duration and for Value` -/

/-- `From<ParseIr<PrimitiveDateTime>>` for `PrimitiveDateTime` is `commit`, for `Value` is
    `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from_eq (x : time.plain_date_time.PlainDateTime) (w : value.Value) :
    time.plain_date_time.PlainDateTime.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok w

/-- [propext, Quot.sound, time.plain_date_time.PlainDateTime] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from_eq
/-- `From<ParseIr<Date>>` for `Date` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrDate.from_eq (x : time.date.Date) (w : value.Value) :
    time.date.Date.Insts.CoreConvertFromParseIrDate.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDate.from (x, w) = ok w

/-- [propext, Quot.sound, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrDate.from_eq
/-- `From<ParseIr<Time>>` for `Time` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrTime.from_eq (x : time.time.Time) (w : value.Value) :
    time.time.Time.Insts.CoreConvertFromParseIrTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrTime.from (x, w) = ok w

/-- [propext, Quot.sound, time.time.Time] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrTime.from_eq
/-- `From<ParseIr<time::Duration>>` for `time::Duration` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrSignedDuration.from_eq (x : time.signed_duration.SignedDuration) (w : value.Value) :
    time.signed_duration.SignedDuration.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok w

/-- [propext, Quot.sound, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrSignedDuration.from_eq
/-! ### `impl From<PrimitiveDateTime> for Value` -/

/-- `From<PrimitiveDateTime> for Value`: total; the `Date` of its fields (the year `as u16`, so
    taken mod `2^16`). -/
recall value.Value.Insts.CoreConvertFromPlainDateTime.from_spec (x : time.plain_date_time.PlainDateTime) :
    value.Value.Insts.CoreConvertFromPlainDateTime.from x ⦃ w =>
      Val.ofValue w = match timeDateTime x with
        | ((y, mo, d), (h, mi, s, us)) => .date (y % 2 ^ 16).toNat mo d h mi s us ⦄

/-- [propext, choice, Quot.sound, Trusted.Date.day, Trusted.Date.month, Trusted.Date.year, Trusted.PrimitiveDateTime.date, Trusted.PrimitiveDateTime.time, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromPlainDateTime.from_spec
/-- Round trip: a valid date-time with a year in `[0, 9999]` reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip (x : time.plain_date_time.PlainDateTime)
    (hv : match timeDateTime x with
      | ((y, mo, d), (h, mi, s, us)) => 0 ≤ y ∧ timeDateValid y mo d ∧ timeTimeValid h mi s us) :
    (do let w ← value.Value.Insts.CoreConvertFromPlainDateTime.from x; value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDateTime x' = timeDateTime x ⦄

/-- [propext, choice, Quot.sound, Trusted.pdtParseDateErr, Trusted.pdtParseDateTime, Trusted.pdtParseDateTimeMicro, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, Trusted.PrimitiveDateTime.date, Trusted.PrimitiveDateTime.date_new, Trusted.PrimitiveDateTime.new, Trusted.PrimitiveDateTime.time, Trusted.PrimitiveDateTime.time_new, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.date.Date, time.plain_date_time.PlainDateTime, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip
/-! ### `impl From<Date> for Value` -/

/-- `From<Date> for Value`: total; the `Date` with zero time (the year taken mod `2^16`). -/
recall value.Value.Insts.CoreConvertFromDate.from_spec (x : time.date.Date) :
    value.Value.Insts.CoreConvertFromDate.from x ⦃ w =>
      Val.ofValue w = match timeDate x with | (y, mo, d) => .date (y % 2 ^ 16).toNat mo d 0 0 0 0 ⦄

/-- [propext, choice, Quot.sound, Trusted.Date.day, Trusted.Date.month, Trusted.Date.year, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDate.from_spec
/-- Round trip: a valid date with a year in `[0, 9999]` reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromDate.roundtrip (x : time.date.Date) (hv : match timeDate x with | (y, mo, d) => 0 ≤ y ∧ timeDateValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromDate.from x; value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDate x' = timeDate x ⦄

/-- [propext, choice, Quot.sound, Trusted.dateParseDate, Trusted.Date.day, Trusted.Date.month, Trusted.Date.ofCalendarDate, Trusted.Date.ofCalendarDate_isSome, Trusted.Date.ofCalendarDate_some, Trusted.Date.year, time.date.Date] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDate.roundtrip
/-! ### `impl From<Time> for Value` -/

/-- `From<Time> for Value`: total; the non-negative `TIME` with 0 days of its fields. -/
recall value.Value.Insts.CoreConvertFromTime.from_spec (x : time.time.Time) :
    value.Value.Insts.CoreConvertFromTime.from x ⦃ w =>
      Val.ofValue w = match timeTime x with | (h, m, s, us) => .time false 0 h m s us ⦄

/-- [propext, choice, Quot.sound, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.time.Time] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromTime.from_spec
/-- Round trip: a valid time reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromTime.roundtrip (x : time.time.Time) (hv : match timeTime x with | (h, m, s, us) => timeTimeValid h m s us) :
    (do let w ← value.Value.Insts.CoreConvertFromTime.from x; value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeTime x' = timeTime x ⦄

/-- [propext, choice, Quot.sound, Trusted.timeFromHmsMicro, Trusted.timeFromHmsMicro_spec, Trusted.timeParseTime, Trusted.timeParseTimeMicro, Trusted.Time.hour, Trusted.Time.microsecond, Trusted.Time.minute, Trusted.Time.second, time.time.Time, time.error.component_range.ComponentRange] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromTime.roundtrip
/-! ### `impl From<time::Duration> for Value` -/

/-- `From<time::Duration> for Value`, where it returns: every duration above `-2^63` seconds
    becomes the `TIME` `signedDurationTime` of its nanoseconds: the sign flag, and the magnitude
    split into days (mod `2^32`: `whole_days() as u32` wraps), hours, minutes, seconds and
    microseconds (nanoseconds below a microsecond are dropped). -/
recall value.Value.Insts.CoreConvertFromSignedDuration.from_spec (x : time.signed_duration.SignedDuration)
    (h : -2 ^ 63 * 10 ^ 9 < Trusted.durNanos x) :
    value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
      Val.ofValue w = signedDurationTime (Trusted.durNanos x) ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.durationSub, Trusted.durationSub_spec, Trusted.durationWholeDays, Trusted.durationWholeDays_spec, Trusted.durationWholeHours, Trusted.durationWholeHours_spec, Trusted.durationWholeMicroseconds, Trusted.durationWholeMicroseconds_spec, Trusted.durationWholeMinutes, Trusted.durationWholeMinutes_spec, Trusted.durationWholeSeconds, Trusted.durationWholeSeconds_spec, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.from_spec
/-- **Upstream panic:** `Value::from` of a `time::Duration` of at most `-2^63` seconds (this
    includes `time::Duration::MIN`) panics: the negation `-x` overflows
    (`checked_neg(..).expect(..)`, signed_duration.rs:1543). Together with `from_spec`: it
    returns iff the duration is above `-2^63` seconds. -/
recall value.Value.Insts.CoreConvertFromSignedDuration.from_panic (x : time.signed_duration.SignedDuration)
    (h : Trusted.durNanos x ≤ -2 ^ 63 * 10 ^ 9) :
    value.Value.Insts.CoreConvertFromSignedDuration.from x = fail .panic

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationDays, Trusted.durationHours, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSub, Trusted.durationWholeDays, Trusted.durationWholeHours, Trusted.durationWholeMicroseconds, Trusted.durationWholeMinutes, Trusted.durationWholeSeconds, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.from_panic
/-- The panic of `from_panic` is reachable: `time::Duration::seconds(i64::MIN)` is such a
    duration. -/
recall value.Value.Insts.CoreConvertFromSignedDuration.from_min_seconds_panics :
    ∃ x, value.convert.trusted.time_duration_seconds (-9223372036854775808)#i64 = ok x ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x = fail .panic

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationDays, Trusted.durationHours, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMinutes, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.durationSub, Trusted.durationWholeDays, Trusted.durationWholeHours, Trusted.durationWholeMicroseconds, Trusted.durationWholeMinutes, Trusted.durationWholeSeconds, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.from_min_seconds_panics
/-- **The days wrap:** `time::Duration::days(2^32)` is sent as the zero `TIME`
    (`whole_days() as u32` truncates). -/
recall value.Value.Insts.CoreConvertFromSignedDuration.from_days_wrap :
    ∃ x, value.convert.trusted.time_duration_days 4294967296#i64 = ok x ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
        Val.ofValue w = .time false 0 0 0 0 0 ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.durationSub, Trusted.durationSub_spec, Trusted.durationWholeDays, Trusted.durationWholeDays_spec, Trusted.durationWholeHours, Trusted.durationWholeHours_spec, Trusted.durationWholeMicroseconds, Trusted.durationWholeMicroseconds_spec, Trusted.durationWholeMinutes, Trusted.durationWholeMinutes_spec, Trusted.durationWholeSeconds, Trusted.durationWholeSeconds_spec, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.from_days_wrap
/-- Round trip `time::Duration → Value → time::Duration`, for every duration that `Value::from`
    accepts (above `-2^63` seconds): the conversion back succeeds, with the nanoseconds of the
    original's magnitude taken modulo `2^32` days and truncated to microseconds, under the
    original's sign. So the nanoseconds are preserved **iff** the duration is a whole number of
    microseconds and shorter than `2^32` days. (time's `Duration` is opaque: equality is stated
    on `durNanos`.) -/
recall value.Value.Insts.CoreConvertFromSignedDuration.roundtrip (x : time.signed_duration.SignedDuration)
    (h : -2 ^ 63 * 10 ^ 9 < Trusted.durNanos x) :
    (do let w ← value.Value.Insts.CoreConvertFromSignedDuration.from x; value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration w) ⦃ r =>
      ∃ y, r = .Ok y ∧
        Trusted.durNanos y = (Trusted.durNanos x).sign *
          (((Trusted.durNanos x).natAbs % (2 ^ 32 * 86400 * 10 ^ 9) / 1000 * 1000 : ℕ) : ℤ) ∧
        (Trusted.durNanos y = Trusted.durNanos x ↔
          ((1000 : ℤ) ∣ Trusted.durNanos x ∧
            (Trusted.durNanos x).natAbs < 2 ^ 32 * 86400 * 10 ^ 9)) ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationAdd, Trusted.durationAdd_spec, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMicroseconds, Trusted.durationMicroseconds_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.durationSub, Trusted.durationSub_spec, Trusted.durationWholeDays, Trusted.durationWholeDays_spec, Trusted.durationWholeHours, Trusted.durationWholeHours_spec, Trusted.durationWholeMicroseconds, Trusted.durationWholeMicroseconds_spec, Trusted.durationWholeMinutes, Trusted.durationWholeMinutes_spec, Trusted.durationWholeSeconds, Trusted.durationWholeSeconds_spec, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.roundtrip
/-- Round trip `Value → time::Duration → Value`, for every `TIME`: both conversions succeed, and
    the result is the original `TIME` **iff** its fields are normalised (hours `< 24`, minutes
    and seconds `< 60`, microseconds `< 10^6`) and it is not a negative zero. (Otherwise the
    result is the normalised `TIME`, `signedDurationTime` of the same nanoseconds, whose days
    can wrap: `Time(false, 4294967295, 24, 0, 0, 0)` is `2^32` days and comes back with 0 days.
    The days never wrap when the fields are normalised.) -/
recall value.Value.Insts.CoreConvertFromSignedDuration.roundtrip_value (neg : Bool) (d : U32) (h m s : U8) (us : U32) :
    ∃ x, value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Time neg d h m s us) = ok (.Ok x) ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
        Val.ofValue w = signedDurationTime (timeSignedNanos neg d.val h.val m.val s.val us.val) ∧
        (w = .Time neg d h m s us ↔
          (h.val < 24 ∧ m.val < 60 ∧ s.val < 60 ∧ us.val < 10 ^ 6 ∧
            (neg = true → timeNanos d.val h.val m.val s.val us.val ≠ 0))) ⦄

/-- [propext, choice, Quot.sound, Trusted.durNanos, Trusted.durationAdd, Trusted.durationAdd_spec, Trusted.durationDays, Trusted.durationDays_spec, Trusted.durationHours, Trusted.durationHours_spec, Trusted.durationLtZero, Trusted.durationLtZero_spec, Trusted.durationMicroseconds, Trusted.durationMicroseconds_spec, Trusted.durationMinutes, Trusted.durationMinutes_spec, Trusted.durationNeg, Trusted.durationNeg_spec, Trusted.durationSeconds, Trusted.durationSeconds_spec, Trusted.durationSub, Trusted.durationSub_spec, Trusted.durationWholeDays, Trusted.durationWholeDays_spec, Trusted.durationWholeHours, Trusted.durationWholeHours_spec, Trusted.durationWholeMicroseconds, Trusted.durationWholeMicroseconds_spec, Trusted.durationWholeMinutes, Trusted.durationWholeMinutes_spec, Trusted.durationWholeSeconds, Trusted.durationWholeSeconds_spec, Trusted.isMatch, Trusted.isMatch_ascii, Trusted.isMatch_loose, time.signed_duration.SignedDuration] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSignedDuration.roundtrip_value
end mysql_common
