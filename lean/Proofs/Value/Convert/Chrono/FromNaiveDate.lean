import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Chrono.ParseIrNaiveDate

/-! Statements for `impl From<NaiveDate> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveDate> for Value`: for a year in `[1000, 9999]`, the `Date` with zero time. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.from_spec (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x ⦃ w =>
      Val.ofValue w = match chronoDate x with
        | (y, mo, d) => .date y.toNat (mo % 256) (d % 256) 0 0 0 0 ⦄ := by
  simp only [chronoDate] at hy
  have h1 : ¬ (1000#i32 > Trusted.NaiveDate.year x) := by scalar_tac
  have h2 : ¬ (Trusted.NaiveDate.year x > 9999#i32) := by scalar_tac
  simp only [value.Value.Insts.CoreConvertFromNaiveDate.from, value.convert.trusted.naive_date_year,
    value.convert.trusted.naive_date_month, value.convert.trusted.naive_date_day, bind_ok, h1, h2,
    ite_false, lift]
  simp [Val.ofValue, chronoDate]
  omega

/-- **Panic.** `From<NaiveDate> for Value` panics for a year outside `[1000, 9999]`. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.from_panic (x : chrono.naive.date.NaiveDate) (hy : ¬ (1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x = fail .panic := by
  simp only [chronoDate] at hy
  simp only [value.Value.Insts.CoreConvertFromNaiveDate.from, value.convert.trusted.naive_date_year, bind_ok]
  by_cases h1 : 1000#i32 > Trusted.NaiveDate.year x
  · simp only [h1, ite_true, ConvDeps.bind_new_display, ConvDeps.bind_arguments_new]
  · have h2 : Trusted.NaiveDate.year x > 9999#i32 := by scalar_tac
    simp only [h1, h2, ite_true, ite_false, ConvDeps.bind_new_display, ConvDeps.bind_arguments_new]

/-- Round trip: a valid date with a year in `[1000, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.roundtrip (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)
    (hv : match chronoDate x with | (y, mo, d) => Trusted.chronoYmdValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDate.from x; value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDate x' = chronoDate x ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromNaiveDate.from_spec x hy)
  intro w hw
  apply WP.spec_mono (chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec w
    (by cases w <;> simp_all [Val.ofValue, Val.bytesAscii]))
  rintro r ⟨_, h2⟩
  rw [hw] at h2
  simp only [chronoDate, Trusted.chronoYmdValid] at hv hy h2 ⊢
  simp only [Val.dateTimeFields] at h2
  obtain ⟨h2, h3⟩ := h2
  have hm : (Trusted.NaiveDate.month x).val % 256 = (Trusted.NaiveDate.month x).val := by omega
  have hd31 := ConvDeps.daysInMonth_le (Trusted.NaiveDate.year x).val (Trusted.NaiveDate.month x).val
  have hd : (Trusted.NaiveDate.day x).val % 256 = (Trusted.NaiveDate.day x).val := by omega
  have hyt : (((Trusted.NaiveDate.year x).val).toNat : ℤ) = (Trusted.NaiveDate.year x).val := by omega
  rw [hm, hd, hyt] at h2 h3
  obtain ⟨x', rfl⟩ := h2.2 hv
  exact ⟨x', rfl, h3 x' rfl⟩

end mysql_common
