import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Time.ParseIrDate

/-! Statements for `impl From<Date> for Value` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Date> for Value`: total; the `Date` with zero time (the year taken mod `2^16`). -/
theorem value.Value.Insts.CoreConvertFromDate.from_spec (x : time.date.Date) :
    value.Value.Insts.CoreConvertFromDate.from x ⦃ w =>
      Val.ofValue w = match timeDate x with | (y, mo, d) => .date (y % 2 ^ 16).toNat mo d 0 0 0 0 ⦄ := by
  obtain ⟨u, hu, huv⟩ := ConvDeps.month_to_u8_val (Trusted.Date.month x)
  simp [value.Value.Insts.CoreConvertFromDate.from, value.convert.trusted.time_date_year,
    value.convert.trusted.time_date_month, value.convert.trusted.time_date_day, hu, lift,
    Val.ofValue, timeDate, huv]

/-- Round trip: a valid date with a year in `[0, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromDate.roundtrip (x : time.date.Date) (hv : match timeDate x with | (y, mo, d) => 0 ≤ y ∧ timeDateValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromDate.from x; value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDate x' = timeDate x ⦄ := by
  obtain ⟨u, hu, huv⟩ := ConvDeps.month_to_u8_val (Trusted.Date.month x)
  simp only [value.Value.Insts.CoreConvertFromDate.from, value.convert.trusted.time_date_year,
    value.convert.trusted.time_date_month, value.convert.trusted.time_date_day, hu, lift, bind_ok]
  apply WP.spec_mono (time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_date _ _ _ _ _ _ _)
  rintro r ⟨_, h2, h3⟩
  simp only [timeDate] at hv
  have hy : ((IScalar.hcast .U16 (Trusted.Date.year x)).val : ℤ) = (Trusted.Date.year x).val := by
    have h0 := hv.1; have h9 := hv.2.2.2.2.1
    rw [IScalar.hcast_val_eq]; simp; omega
  obtain ⟨x', rfl⟩ := h2.2 (by rw [hy, huv]; exact hv.2)
  refine ⟨x', rfl, ?_⟩
  rw [h3 x' rfl, hy, huv]; rfl

end mysql_common
