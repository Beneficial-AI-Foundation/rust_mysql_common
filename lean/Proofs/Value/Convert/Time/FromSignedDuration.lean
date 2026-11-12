import Defs

/-! Statements for `impl From<time::Duration> for Value` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<time::Duration> for Value` (glue level: time's `Duration` arithmetic is opaque and may
    panic): if it returns, it is a `TIME` whose sign is whether the duration is negative. -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_sign (x : time.signed_duration.SignedDuration) (w : value.Value) (h : value.Value.Insts.CoreConvertFromSignedDuration.from x = ok w) :
    ∃ d hh m s us, w = .Time (Trusted.durationLtZero x) d hh m s us := by
  sorry

end mysql_common
