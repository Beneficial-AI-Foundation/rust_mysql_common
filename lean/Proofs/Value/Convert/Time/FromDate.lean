import Defs

/-! Statements for `impl From<Date> for Value` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Date> for Value`: total; the `Date` with zero time (the year taken mod `2^16`). -/
theorem value.Value.Insts.CoreConvertFromDate.from_spec (x : time.date.Date) :
    value.Value.Insts.CoreConvertFromDate.from x ⦃ w =>
      Val.ofValue w = match timeDate x with | (y, mo, d) => .date (y % 2 ^ 16).toNat mo d 0 0 0 0 ⦄ := by
  sorry

/-- Round trip: a valid date with a year in `[0, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromDate.roundtrip (x : time.date.Date) (hv : match timeDate x with | (y, mo, d) => 0 ≤ y ∧ timeDateValid y mo d) :
    (do let w ← value.Value.Insts.CoreConvertFromDate.from x; value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDate x' = timeDate x ⦄ := by
  sorry

end mysql_common
