import Defs

/-! Statements for `impl From<NaiveTime> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveTime> for Value`: the non-negative `TIME` with 0 days of its fields (taken mod 256 by
    `as u8`; nanoseconds truncated to microseconds). -/
theorem value.Value.Insts.CoreConvertFromNaiveTime.from_spec (x : chrono.naive.time.NaiveTime) :
    value.Value.Insts.CoreConvertFromNaiveTime.from x ⦃ w =>
      Val.ofValue w = match chronoTime x with
        | (h, m, s, ns) => .time false 0 (h % 256) (m % 256) (s % 256) (ns / 1000) ⦄ := by
  sorry

/-- Round trip: a valid time reads back with the same fields, nanoseconds truncated to
    microseconds. -/
theorem value.Value.Insts.CoreConvertFromNaiveTime.roundtrip (x : chrono.naive.time.NaiveTime)
    (hv : match chronoTime x with | (h, m, s, ns) => Trusted.chronoHmsMicroValid h m s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveTime.from x; value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoTime x' = match chronoTime x with
        | (h, m, s, ns) => (h, m, s, ns / 1000 * 1000) ⦄ := by
  sorry

end mysql_common
