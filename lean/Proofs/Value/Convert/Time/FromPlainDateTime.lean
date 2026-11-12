import Defs

/-! Statements for `impl From<PrimitiveDateTime> for Value` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<PrimitiveDateTime> for Value`: total; the `Date` of its fields (the year `as u16`, so
    taken mod `2^16`). -/
theorem value.Value.Insts.CoreConvertFromPlainDateTime.from_spec (x : time.plain_date_time.PlainDateTime) :
    value.Value.Insts.CoreConvertFromPlainDateTime.from x ⦃ w =>
      Val.ofValue w = match timeDateTime x with
        | ((y, mo, d), (h, mi, s, us)) => .date (y % 2 ^ 16).toNat mo d h mi s us ⦄ := by
  sorry

/-- Round trip: a valid date-time with a year in `[0, 9999]` reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromPlainDateTime.roundtrip (x : time.plain_date_time.PlainDateTime)
    (hv : match timeDateTime x with
      | ((y, mo, d), (h, mi, s, us)) => 0 ≤ y ∧ timeDateValid y mo d ∧ timeTimeValid h mi s us) :
    (do let w ← value.Value.Insts.CoreConvertFromPlainDateTime.from x; value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeDateTime x' = timeDateTime x ⦄ := by
  sorry

end mysql_common
