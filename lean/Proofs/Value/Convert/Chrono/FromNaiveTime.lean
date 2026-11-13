import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Chrono.ParseIrNaiveTime

/-! Statements for `impl From<NaiveTime> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveTime> for Value`: the non-negative `TIME` with 0 days of its fields (taken mod 256 by
    `as u8`; nanoseconds truncated to microseconds). -/
theorem value.Value.Insts.CoreConvertFromNaiveTime.from_spec (x : chrono.naive.time.NaiveTime) :
    value.Value.Insts.CoreConvertFromNaiveTime.from x ⦃ w =>
      Val.ofValue w = match chronoTime x with
        | (h, m, s, ns) => .time false 0 (h % 256) (m % 256) (s % 256) (ns / 1000) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromNaiveTime.from, value.convert.trusted.naive_time_hour,
    value.convert.trusted.naive_time_minute, value.convert.trusted.naive_time_second,
    value.convert.trusted.naive_time_nanosecond, bind_ok, lift]
  step*
  simp [Val.ofValue, chronoTime, *]

/-- Round trip: a valid time reads back with the same fields, nanoseconds truncated to
    microseconds. -/
theorem value.Value.Insts.CoreConvertFromNaiveTime.roundtrip (x : chrono.naive.time.NaiveTime)
    (hv : match chronoTime x with | (h, m, s, ns) => Trusted.chronoHmsMicroValid h m s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveTime.from x; value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoTime x' = match chronoTime x with
        | (h, m, s, ns) => (h, m, s, ns / 1000 * 1000) ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromNaiveTime.from_spec x)
  intro w hw
  apply WP.spec_mono (chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime.from_value_opt_spec w
    (by cases w <;> simp_all [Val.ofValue, Val.timeTextPanics]))
  rintro r ⟨_, h2⟩
  rw [hw] at h2
  simp only [chronoTime, Trusted.chronoHmsMicroValid] at hv h2 ⊢
  simp only [Val.timeOfDayFields] at h2
  obtain ⟨h2, h3⟩ := h2
  have e1 : (Trusted.NaiveTime.hour x).val % 256 = (Trusted.NaiveTime.hour x).val := by omega
  have e2 : (Trusted.NaiveTime.minute x).val % 256 = (Trusted.NaiveTime.minute x).val := by omega
  have e3 : (Trusted.NaiveTime.second x).val % 256 = (Trusted.NaiveTime.second x).val := by omega
  rw [e1, e2, e3] at h2 h3
  obtain ⟨x', rfl⟩ := h2.2 hv
  exact ⟨x', rfl, h3 x' rfl⟩

end mysql_common
