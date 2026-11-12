import Defs

/-! Statements for `impl From<NaiveDate> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveDate> for Value`: for a year in `[1000, 9999]`, the `Date` with zero time. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.from_spec (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x ⦃ w =>
      Val.ofValue w = match chronoDate x with
        | (y, mo, d) => .date y.toNat (mo % 256) (d % 256) 0 0 0 0 ⦄ := by
  sorry

/-- **Panic.** `From<NaiveDate> for Value` panics for a year outside `[1000, 9999]`. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.from_panic (x : chrono.naive.date.NaiveDate) (hy : ¬ (1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDate.from x = fail .panic := by
  sorry

/-- Round trip: a valid date with a year in `[1000, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromNaiveDate.roundtrip (x : chrono.naive.date.NaiveDate) (hy : 1000 ≤ (chronoDate x).1 ∧ (chronoDate x).1 ≤ 9999)
    (hv : match chronoDate x with | (y, mo, d) => Trusted.chronoYmdValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDate.from x; value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDate x' = chronoDate x ⦄ := by
  sorry

end mysql_common
