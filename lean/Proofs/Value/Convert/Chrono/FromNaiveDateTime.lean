import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Chrono.ParseIrNaiveDateTime

/-! Statements for `impl From<NaiveDateTime> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveDateTime> for Value`: for a year in `[1000, 9999]`, the `Date` of its fields
    (month, day, hour, minute, second taken mod 256 by `as u8`; nanoseconds truncated to
    microseconds). -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.from_spec (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x ⦃ w =>
      Val.ofValue w = match chronoDateTime x with
        | ((y, mo, d), (h, mi, s, ns)) =>
          .date y.toNat (mo % 256) (d % 256) (h % 256) (mi % 256) (s % 256) (ns / 1000) ⦄ := by
  simp only [chronoDateTime, chronoDate] at hy
  have h1 : ¬ (1000#i32 > Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x)) := by scalar_tac
  have h2 : ¬ (Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x) > 9999#i32) := by scalar_tac
  simp only [value.Value.Insts.CoreConvertFromNaiveDateTime.from, value.convert.trusted.naive_date_year,
    value.convert.trusted.naive_date_month, value.convert.trusted.naive_date_day,
    value.convert.trusted.naive_datetime_date, value.convert.trusted.naive_datetime_time,
    value.convert.trusted.naive_time_hour, value.convert.trusted.naive_time_minute,
    value.convert.trusted.naive_time_second, value.convert.trusted.naive_time_nanosecond,
    bind_ok, h1, h2, ite_false, lift]
  step*
  simp [Val.ofValue, chronoDateTime, chronoDate, chronoTime, *]
  omega

/-- **Panic.** `From<NaiveDateTime> for Value` panics for a year outside `[1000, 9999]`. -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.from_panic (x : chrono.naive.datetime.NaiveDateTime) (hy : ¬ (1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x = fail .panic := by
  simp only [chronoDateTime, chronoDate] at hy
  simp only [value.Value.Insts.CoreConvertFromNaiveDateTime.from, value.convert.trusted.naive_date_year,
    value.convert.trusted.naive_datetime_date, value.convert.trusted.naive_datetime_time, bind_ok]
  by_cases h1 : 1000#i32 > Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x)
  · simp only [h1, ite_true, ConvDeps.bind_new_display, ConvDeps.bind_arguments_new]
  · have h2 : Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x) > 9999#i32 := by scalar_tac
    simp only [h1, h2, ite_true, ite_false, ConvDeps.bind_new_display, ConvDeps.bind_arguments_new]

/-- Round trip: a valid date-time with a year in `[1000, 9999]` reads back with the same fields,
    nanoseconds truncated to microseconds. -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.roundtrip (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)
    (hv : match chronoDateTime x with
      | ((y, mo, d), (h, mi, s, ns)) =>
        Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDateTime.from x; value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDateTime x' = match chronoDateTime x with
        | (dt, (h, mi, s, ns)) => (dt, (h, mi, s, ns / 1000 * 1000)) ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromNaiveDateTime.from_spec x hy)
  intro w hw
  apply WP.spec_mono (chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_spec w
    (by cases w <;> simp_all [Val.ofValue, Val.datetimeTextPanics]))
  rintro r ⟨_, h2⟩
  rw [hw] at h2
  simp only [chronoDateTime, chronoDate, chronoTime, Trusted.chronoYmdValid, Trusted.chronoHmsMicroValid] at hv hy h2 ⊢
  simp only [Val.dateTimeFields] at h2
  obtain ⟨h2, h3⟩ := h2
  have hd31 := ConvDeps.daysInMonth_le (Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x)).val
    (Trusted.NaiveDate.month (Trusted.NaiveDateTime.date x)).val
  have e1 : (Trusted.NaiveDate.month (Trusted.NaiveDateTime.date x)).val % 256 =
    (Trusted.NaiveDate.month (Trusted.NaiveDateTime.date x)).val := by omega
  have e2 : (Trusted.NaiveDate.day (Trusted.NaiveDateTime.date x)).val % 256 =
    (Trusted.NaiveDate.day (Trusted.NaiveDateTime.date x)).val := by omega
  have e3 : (Trusted.NaiveTime.hour (Trusted.NaiveDateTime.time x)).val % 256 =
    (Trusted.NaiveTime.hour (Trusted.NaiveDateTime.time x)).val := by omega
  have e4 : (Trusted.NaiveTime.minute (Trusted.NaiveDateTime.time x)).val % 256 =
    (Trusted.NaiveTime.minute (Trusted.NaiveDateTime.time x)).val := by omega
  have e5 : (Trusted.NaiveTime.second (Trusted.NaiveDateTime.time x)).val % 256 =
    (Trusted.NaiveTime.second (Trusted.NaiveDateTime.time x)).val := by omega
  have hyt : (((Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x)).val).toNat : ℤ) =
    (Trusted.NaiveDate.year (Trusted.NaiveDateTime.date x)).val := by omega
  rw [e1, e2, e3, e4, e5, hyt] at h2 h3
  obtain ⟨x', rfl⟩ := h2.2 hv
  exact ⟨x', rfl, h3 x' rfl⟩

end mysql_common
