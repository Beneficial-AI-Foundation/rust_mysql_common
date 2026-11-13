import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Time.ParseIrPlainDateTime

/-! Statements for `impl From<PrimitiveDateTime> for Value` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<PrimitiveDateTime> for Value`: total; the `Date` of its fields (the year `as u16`, so
    taken mod `2^16`). -/
theorem value.Value.Insts.CoreConvertFromPlainDateTime.from_spec (x : time.plain_date_time.PlainDateTime) :
    value.Value.Insts.CoreConvertFromPlainDateTime.from x ⦃ w =>
      Val.ofValue w = match timeDateTime x with
        | ((y, mo, d), (h, mi, s, us)) => .date (y % 2 ^ 16).toNat mo d h mi s us ⦄ := by
  obtain ⟨u, hu, huv⟩ := ConvDeps.month_to_u8_val (Trusted.Date.month (Trusted.PrimitiveDateTime.date x))
  simp [value.Value.Insts.CoreConvertFromPlainDateTime.from, value.convert.trusted.time_date_year,
    value.convert.trusted.time_date_month, value.convert.trusted.time_date_day, hu, lift,
    value.convert.trusted.time_primitive_date_time_date, value.convert.trusted.time_primitive_date_time_time,
    value.convert.trusted.time_time_hour, value.convert.trusted.time_time_minute,
    value.convert.trusted.time_time_second, value.convert.trusted.time_time_microsecond,
    Val.ofValue, timeDateTime, timeDate, timeTime, huv]

/-- Round trip: a valid date-time with a year in `[0, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip (x : time.plain_date_time.PlainDateTime)
    (hv : match timeDateTime x with
      | ((y, mo, d), (h, mi, s, us)) => 0 ≤ y ∧ timeDateValid y mo d ∧ timeTimeValid h mi s us) :
    (do let w ← value.Value.Insts.CoreConvertFromPlainDateTime.from x; value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDateTime x' = timeDateTime x ⦄ := by
  obtain ⟨u, hu, huv⟩ := ConvDeps.month_to_u8_val (Trusted.Date.month (Trusted.PrimitiveDateTime.date x))
  simp only [value.Value.Insts.CoreConvertFromPlainDateTime.from, value.convert.trusted.time_date_year,
    value.convert.trusted.time_date_month, value.convert.trusted.time_date_day, hu, lift, bind_ok,
    value.convert.trusted.time_primitive_date_time_date, value.convert.trusted.time_primitive_date_time_time,
    value.convert.trusted.time_time_hour, value.convert.trusted.time_time_minute,
    value.convert.trusted.time_time_second, value.convert.trusted.time_time_microsecond]
  apply WP.spec_mono (time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date _ _ _ _ _ _ _)
  rintro r ⟨_, h2, h3⟩
  simp only [timeDateTime, timeDate, timeTime] at hv
  have hy : ((IScalar.hcast .U16 (Trusted.Date.year (Trusted.PrimitiveDateTime.date x))).val : ℤ) =
      (Trusted.Date.year (Trusted.PrimitiveDateTime.date x)).val := by
    have h0 := hv.1; have h9 := hv.2.1.2.2.2.1
    rw [IScalar.hcast_val_eq]; simp; omega
  obtain ⟨x', rfl⟩ := h2.2 (by rw [hy, huv]; exact hv.2)
  refine ⟨x', rfl, ?_⟩
  rw [h3 x' rfl, hy, huv]; rfl

end mysql_common
