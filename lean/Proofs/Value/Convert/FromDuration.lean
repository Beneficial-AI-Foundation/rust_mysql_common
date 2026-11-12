import Defs

/-! Statements for `impl From<Duration> for Value` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Duration> for Value`: the non-negative `TIME` `durationTime` (microseconds rounded half
    up, not carried; days truncated to `u32`). The rounding `(nanos + 500) / 1000` is patch 50's;
    it equals upstream's `(nanos as f64 / 1000.0).round()` for every `nanos < 10^9`. -/
theorem value.Value.Insts.CoreConvertFromDuration.from_spec (d : core.time.Duration) :
    value.Value.Insts.CoreConvertFromDuration.from d ⦃ w =>
      Val.ofValue w = durationTime d.secs.val d.nanos.val ⦄ := by
  sorry

/-- Round trip: `from_value_opt::<Duration>(Value::from(d))` is `d` rounded to the nearest
    microsecond (half up), modulo `2^32` days. -/
theorem value.Value.Insts.CoreConvertFromDuration.roundtrip (d : core.time.Duration) :
    (do let w ← value.Value.Insts.CoreConvertFromDuration.from d; value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration w) ⦃ r =>
      ∃ d', r = .Ok d' ∧
        durNanos d' = (d.secs.val % (86400 * 2 ^ 32)) * 10 ^ 9 + (d.nanos.val + 500) / 1000 * 1000 ⦄ := by
  sorry

end mysql_common
