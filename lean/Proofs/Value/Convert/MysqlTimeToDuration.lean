import Defs
import Proofs.Util.ConvBytesTime

/-! Statements for `fn mysql_time_to_duration` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

namespace mysql_common

/-- `mysql_time_to_duration` (private): the duration of `days hours:minutes:seconds.micros`
    (`timeNanos`, fields not range-checked), when `microseconds * 1000` fits in a `u32`. -/
theorem value.convert.mysql_time_to_duration_spec (d : U32) (h m s : U8) (us : U32) (hus : us.val * 1000 < 2 ^ 32) :
    value.convert.mysql_time_to_duration d h m s us ⦃ x => durNanos x = timeNanos d.val h.val m.val s.val us.val ⦄ := by
  unfold value.convert.mysql_time_to_duration
  step*
  simp only [timeNanos, x_post, secs_post, i11_post, i10_post, i9_post, i8_post, i7_post, i6_post,
    i5_post, i4_post, i3_post, i2_post, i1_post, i_post, nanos_post,
    core.convert.num.FromU64U8.from_val_eq, core.convert.num.FromU64U32.from_val_eq]
  ring

/-- **Upstream bug.** `mysql_time_to_duration` overflows (`microseconds * 1000` in `u32`) when
    `microseconds > 4294967`: a panic in debug builds (the model), a wrong duration in release
    builds. -/
theorem value.convert.mysql_time_to_duration_overflow (d : U32) (h m s : U8) (us : U32) (hus : 2 ^ 32 ≤ us.val * 1000) :
    value.convert.mysql_time_to_duration d h m s us = fail .integerOverflow := by
  unfold value.convert.mysql_time_to_duration
  rw [umul_overflow us 1000#u32 (by simpa using hus)]
  simp

end mysql_common
