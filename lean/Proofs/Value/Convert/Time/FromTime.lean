import Defs

/-! Statements for `impl From<Time> for Value` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Time> for Value`: total; the non-negative `TIME` with 0 days of its fields. -/
theorem value.Value.Insts.CoreConvertFromTime.from_spec (x : time.time.Time) :
    value.Value.Insts.CoreConvertFromTime.from x ⦃ w =>
      Val.ofValue w = match timeTime x with | (h, m, s, us) => .time false 0 h m s us ⦄ := by
  sorry

/-- Round trip: a valid time reads back with the same fields. -/
theorem value.Value.Insts.CoreConvertFromTime.roundtrip (x : time.time.Time) (hv : match timeTime x with | (h, m, s, us) => timeTimeValid h m s us) :
    (do let w ← value.Value.Insts.CoreConvertFromTime.from x; value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ timeTime x' = timeTime x ⦄ := by
  sorry

end mysql_common
