import Proofs.Value.Convert.Chrono.ParseIrNaiveDateTime
import Proofs.Value.Convert.Chrono.ParseIrNaiveDate
import Proofs.Value.Convert.Chrono.ParseIrNaiveTime
import Proofs.Value.Convert.Chrono.FromParseIr
import Proofs.Value.Convert.Chrono.FromNaiveDateTime
import Proofs.Value.Convert.Chrono.FromNaiveDate
import Proofs.Value.Convert.Chrono.FromNaiveTime

/-!
# `src/value/convert/chrono.rs`
    `FromValue` and `From<_> for Value` for chrono's `NaiveDateTime`, `NaiveDate`, `NaiveTime`.
    chrono's types are opaque; the statements speak about them through their getters
    (`chronoDate`, `chronoTime`, `chronoDateTime`).

    **Configuration.** As in `Specs/Io.lean` (feature `chrono`, chrono 0.4.45).

    **Definitions used.** `Defs/Convert.lean` (`Val.dateTimeFields`, `Val.timeOfDayFields`,
    `Val.bytesAscii`, `datetimeStringRead`, `timeStringRead`, `chronoDate`, `chronoTime`,
    `chronoDateTime`), `Trusted.chronoYmdValid`, `Trusted.chronoHmsMicroValid` (chrono's validity
    rules, `FunsExternal.lean`), `Defs/Value.lean`, `Defs/Bytes.lean`.

    **Trusted axioms these statements rest on** (`FunsExternal.lean`, namespace `Trusted`):
    `NaiveDate.ofYmd`, `NaiveDate.year`/`month`/`day`, `NaiveDate.ofYmd_isSome`,
    `NaiveDate.ofYmd_some`, `NaiveTime.ofHmsMicro`, `NaiveTime.hour`/`minute`/`second`/`nanosecond`,
    `NaiveTime.ofHmsMicro_isSome`, `NaiveTime.ofHmsMicro_some`, `NaiveDateTime.new`/`date`/`time`,
    `NaiveDateTime.date_new`, `NaiveDateTime.time_new`; and, for reading from `Bytes`,
    `isMatch`/`isMatch_ascii` (the regexes, see `Specs/Value/Convert.lean`).

    **Round trips** are stated up to the getters (there is no extensionality axiom for chrono's
    types), with the hypothesis that the value's fields are valid: true of every value chrono can
    build, but not axiomatized.

    **Behaviour to note.**
    * `From<NaiveDateTime>`/`From<NaiveDate> for Value` **panic** for years outside
      `[1000, 9999]`, although chrono and MySQL `DATE` (`1000-01-01` to `9999-12-31` is only the
      *supported* range) allow others.
    * `FromValue for NaiveDate` accepts a `DATETIME` (value or text) and silently drops the time.
    * `FromValue for NaiveTime` accepts only a non-negative (sign flag false) `TIME` with 0 days (no `-00:00:01`, no
      hours ≥ 24), and a leap second (micros in `[10^6, 2·10^6)` at second 59) as chrono does.
    * Sub-microsecond nanoseconds are truncated by `From<_> for Value`.
    * Reading from `Bytes` needs ASCII input (the non-ASCII panic of the string parsers).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl TryFrom<Value> for ParseIr<NaiveDateTime>` -/

/-- `TryFrom<Value> for ParseIr<NaiveDateTime>`: a `Date`, or `Bytes` holding a text
    `DATE`/`DATETIME` literal (ASCII hypothesis), converts exactly when chrono accepts the date
    and the time, to the date-time with these fields, keeping the original value; anything else
    is an error carrying the value. -/
recall value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, h, mi, s, us) =>
        ((∃ p, r = .Ok p) ↔
          Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s us) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoDateTime x = (((y : ℤ), mo, d), (h, mi, s, us * 1000))
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, h, mi, s, us) =>
        ((∃ p, r = .Ok p) ↔
          Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s us) ∧
        ∀ x, r = .Ok x → chronoDateTime x = (((y : ℤ), mo, d), (h, mi, s, us * 1000))
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_spec`

/-! ### `impl TryFrom<Value> for ParseIr<NaiveDate>` -/

/-- `TryFrom<Value> for ParseIr<NaiveDate>`: as for `NaiveDateTime`, but only the date fields
    are read and checked (a time part is ignored). -/
recall value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x, r = .Ok x → chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec`

/-! ### `impl TryFrom<Value> for ParseIr<NaiveTime>` -/

/-- `TryFrom<Value> for ParseIr<NaiveTime>`: a non-negative (sign flag false) `TIME` with 0 days, or `Bytes` holding a
    non-negative text `TIME` literal (ASCII hypothesis), converts exactly when chrono accepts the
    time; anything else is an error carrying the value. -/
recall value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x, r = .Ok x → chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime.from_value_opt_spec`

/-! ### `impl From<ParseIr<_>> for NaiveDateTime, NaiveDate, NaiveTime and for Value` -/

/-- `From<ParseIr<NaiveDateTime>>` for `NaiveDateTime` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrNaiveDateTime.from_eq (x : chrono.naive.datetime.NaiveDateTime) (w : value.Value) :
    chrono.naive.datetime.NaiveDateTime.Insts.CoreConvertFromParseIrNaiveDateTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveDateTime.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrNaiveDateTime.from_eq`

/-- `From<ParseIr<NaiveDate>>` for `NaiveDate` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrNaiveDate.from_eq (x : chrono.naive.date.NaiveDate) (w : value.Value) :
    chrono.naive.date.NaiveDate.Insts.CoreConvertFromParseIrNaiveDate.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveDate.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrNaiveDate.from_eq`

/-- `From<ParseIr<NaiveTime>>` for `NaiveTime` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrNaiveTime.from_eq (x : chrono.naive.time.NaiveTime) (w : value.Value) :
    chrono.naive.time.NaiveTime.Insts.CoreConvertFromParseIrNaiveTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveTime.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrNaiveTime.from_eq`

/-! ### `impl From<NaiveDateTime> for Value` -/

/-- `From<NaiveDateTime> for Value`: for a year in `[1000, 9999]`, the `Date` of its fields
    (month, day, hour, minute, second taken mod 256 by `as u8`; nanoseconds truncated to
    microseconds). -/
recall value.Value.Insts.CoreConvertFromNaiveDateTime.from_spec (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x ⦃ w =>
      Val.ofValue w = match chronoDateTime x with
        | ((y, mo, d), (h, mi, s, ns)) =>
          .date y.toNat (mo % 256) (d % 256) (h % 256) (mi % 256) (s % 256) (ns / 1000) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDateTime.from_spec`

/-- **Panic.** `From<NaiveDateTime> for Value` panics for a year outside `[1000, 9999]`. -/
recall value.Value.Insts.CoreConvertFromNaiveDateTime.from_panic (x : chrono.naive.datetime.NaiveDateTime) (hy : ¬ (1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDateTime.from_panic`

/-- Round trip: a valid date-time with a year in `[1000, 9999]` reads back with the same fields,
    nanoseconds truncated to microseconds. -/
recall value.Value.Insts.CoreConvertFromNaiveDateTime.roundtrip (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)
    (hv : match chronoDateTime x with
      | ((y, mo, d), (h, mi, s, ns)) =>
        Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDateTime.from x; value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDateTime x' = match chronoDateTime x with
        | (dt, (h, mi, s, ns)) => (dt, (h, mi, s, ns / 1000 * 1000)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDateTime.roundtrip`

/-! ### `impl From<NaiveDate> for Value` -/

/-- `From<NaiveDate> for Value`: for a year in `[1000, 9999]`, the `Date` with zero time. -/
recall value.Value.Insts.CoreConvertFromNaiveDate.from_spec (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x ⦃ w =>
      Val.ofValue w = match chronoDate x with
        | (y, mo, d) => .date y.toNat (mo % 256) (d % 256) 0 0 0 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDate.from_spec`

/-- **Panic.** `From<NaiveDate> for Value` panics for a year outside `[1000, 9999]`. -/
recall value.Value.Insts.CoreConvertFromNaiveDate.from_panic (x : chrono.naive.date.NaiveDate) (hy : ¬ (1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDate.from_panic`

/-- Round trip: a valid date with a year in `[1000, 9999]` reads back with the same fields. -/
recall value.Value.Insts.CoreConvertFromNaiveDate.roundtrip (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)
    (hv : match chronoDate x with | (y, mo, d) => Trusted.chronoYmdValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDate.from x; value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDate x' = chronoDate x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveDate.roundtrip`

/-! ### `impl From<NaiveTime> for Value` -/

/-- `From<NaiveTime> for Value`: the non-negative `TIME` with 0 days of its fields (taken mod 256 by
    `as u8`; nanoseconds truncated to microseconds). -/
recall value.Value.Insts.CoreConvertFromNaiveTime.from_spec (x : chrono.naive.time.NaiveTime) :
    value.Value.Insts.CoreConvertFromNaiveTime.from x ⦃ w =>
      Val.ofValue w = match chronoTime x with
        | (h, m, s, ns) => .time false 0 (h % 256) (m % 256) (s % 256) (ns / 1000) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveTime.from_spec`

/-- Round trip: a valid time reads back with the same fields, nanoseconds truncated to
    microseconds. -/
recall value.Value.Insts.CoreConvertFromNaiveTime.roundtrip (x : chrono.naive.time.NaiveTime)
    (hv : match chronoTime x with | (h, m, s, ns) => Trusted.chronoHmsMicroValid h m s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveTime.from x; value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoTime x' = match chronoTime x with
        | (h, m, s, ns) => (h, m, s, ns / 1000 * 1000) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromNaiveTime.roundtrip`

end mysql_common
