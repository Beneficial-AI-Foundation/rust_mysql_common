import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl From<time::Duration> for Value` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<time::Duration> for Value` (partial, glue level: time's `Duration` arithmetic is opaque
    and may panic, e.g. on `Duration::MIN`): if it returns, it is a `TIME` whose sign is whether the duration is negative. -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_sign (x : time.signed_duration.SignedDuration) (w : value.Value) (h : value.Value.Insts.CoreConvertFromSignedDuration.from x = ok w) :
    ∃ d hh m s us, w = .Time (Trusted.durationLtZero x) d hh m s us := by
  simp only [value.Value.Insts.CoreConvertFromSignedDuration.from,
    value.convert.trusted.time_duration_lt_zero, bind_ok] at h
  repeat (obtain ⟨_, _, h⟩ := ConvDeps.bind_eq_ok_inv h)
  simp only [ok.injEq] at h
  exact ⟨_, _, _, _, _, h.symm⟩

end mysql_common
