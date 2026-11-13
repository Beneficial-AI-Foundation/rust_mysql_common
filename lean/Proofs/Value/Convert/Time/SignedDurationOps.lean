import Defs
import Proofs.Util.ConvDeps

/-! Helper lemmas about the `time::Duration` operations of `value::convert::trusted`, derived
    from the `Trusted.duration*_spec` axioms (`FunsExternal.lean`). Used by
    `ParseIrSignedDuration.lean` and `FromSignedDuration.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common.TimeDur

open Trusted

/-- The representable range of a `time::Duration`, from `whole_seconds` being an `i64`:
    `Duration::MIN ..= Duration::MAX`. -/
theorem durNanos_range (a : time.signed_duration.SignedDuration) :
    -2 ^ 63 * 10 ^ 9 - 999999999 ≤ durNanos a ∧ durNanos a ≤ (2 ^ 63 - 1) * 10 ^ 9 + 999999999 := by
  have h := durationWholeSeconds_spec a
  have hb : -2 ^ 63 ≤ (durationWholeSeconds a).val ∧ (durationWholeSeconds a).val < 2 ^ 63 := by
    scalar_tac
  rw [h, Int.tdiv_eq_ediv, show Int.sign (10 ^ 9 : Int) = 1 from by norm_num] at hb
  split at hb <;> omega

/-! ## Casts -/

theorem u32_hcast_i64_val (y : U32) : (UScalar.hcast .I64 y).val = y.val := by
  rw [UScalar.hcast_val_eq]
  apply Int.bmod_eq_of_le <;> scalar_tac

theorem u8_hcast_i64_val (y : U8) : (UScalar.hcast .I64 y).val = y.val := by
  rw [UScalar.hcast_val_eq]
  apply Int.bmod_eq_of_le <;> scalar_tac

/-! ## Constructors -/

theorem days_ok (x : I64) (h : -2 ^ 63 ≤ x.val * 86400 ∧ x.val * 86400 < 2 ^ 63) :
    ∃ d, value.convert.trusted.time_duration_days x = ok d ∧
      durNanos d = x.val * 86400 * 10 ^ 9 := (durationDays_spec x).1 h

theorem hours_ok (x : I64) (h : -2 ^ 63 ≤ x.val * 3600 ∧ x.val * 3600 < 2 ^ 63) :
    ∃ d, value.convert.trusted.time_duration_hours x = ok d ∧
      durNanos d = x.val * 3600 * 10 ^ 9 := (durationHours_spec x).1 h

theorem minutes_ok (x : I64) (h : -2 ^ 63 ≤ x.val * 60 ∧ x.val * 60 < 2 ^ 63) :
    ∃ d, value.convert.trusted.time_duration_minutes x = ok d ∧
      durNanos d = x.val * 60 * 10 ^ 9 := (durationMinutes_spec x).1 h

theorem seconds_ok (x : I64) :
    ∃ d, value.convert.trusted.time_duration_seconds x = ok d ∧
      durNanos d = x.val * 10 ^ 9 := durationSeconds_spec x

theorem microseconds_ok (x : I64) :
    ∃ d, value.convert.trusted.time_duration_microseconds x = ok d ∧
      durNanos d = x.val * 1000 := durationMicroseconds_spec x

/-! ## Arithmetic -/

theorem add_ok (a b : time.signed_duration.SignedDuration)
    (h : -2 ^ 63 * 10 ^ 9 - 999999999 ≤ durNanos a + durNanos b ∧
      durNanos a + durNanos b ≤ (2 ^ 63 - 1) * 10 ^ 9 + 999999999) :
    ∃ d, value.convert.trusted.time_duration_add a b = ok d ∧
      durNanos d = durNanos a + durNanos b := (durationAdd_spec a b).1 h

/-- Subtracting a smaller non-negative duration never panics. -/
theorem sub_ok (a b : time.signed_duration.SignedDuration) (hb : 0 ≤ durNanos b)
    (hab : durNanos b ≤ durNanos a) :
    ∃ d, value.convert.trusted.time_duration_sub a b = ok d ∧
      durNanos d = durNanos a - durNanos b := by
  apply (durationSub_spec a b).1
  have ha := durNanos_range a
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg hb]
  omega

theorem neg_ok (a : time.signed_duration.SignedDuration) (h : -2 ^ 63 * 10 ^ 9 < durNanos a) :
    ∃ d, value.convert.trusted.time_duration_neg a = ok d ∧ durNanos d = -durNanos a :=
  (durationNeg_spec a).1 h

theorem neg_panic (a : time.signed_duration.SignedDuration) (h : durNanos a ≤ -2 ^ 63 * 10 ^ 9) :
    value.convert.trusted.time_duration_neg a = fail .panic := (durationNeg_spec a).2 h

/-! ## Getters of a non-negative duration -/

theorem whole_days_val (a : time.signed_duration.SignedDuration) (h : 0 ≤ durNanos a) :
    (durationWholeDays a).val = durNanos a / 10 ^ 9 / 86400 := by
  rw [durationWholeDays_spec, Int.tdiv_eq_ediv_of_nonneg h, Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem whole_hours_val (a : time.signed_duration.SignedDuration) (h : 0 ≤ durNanos a) :
    (durationWholeHours a).val = durNanos a / 10 ^ 9 / 3600 := by
  rw [durationWholeHours_spec, Int.tdiv_eq_ediv_of_nonneg h, Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem whole_minutes_val (a : time.signed_duration.SignedDuration) (h : 0 ≤ durNanos a) :
    (durationWholeMinutes a).val = durNanos a / 10 ^ 9 / 60 := by
  rw [durationWholeMinutes_spec, Int.tdiv_eq_ediv_of_nonneg h,
    Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem whole_seconds_val (a : time.signed_duration.SignedDuration) (h : 0 ≤ durNanos a) :
    (durationWholeSeconds a).val = durNanos a / 10 ^ 9 := by
  rw [durationWholeSeconds_spec, Int.tdiv_eq_ediv_of_nonneg h]

theorem whole_microseconds_val (a : time.signed_duration.SignedDuration) (h : 0 ≤ durNanos a) :
    (durationWholeMicroseconds a).val = durNanos a / 1000 := by
  rw [durationWholeMicroseconds_spec, Int.tdiv_eq_ediv_of_nonneg h,
    Int.tmod_eq_emod_of_nonneg h, Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

end mysql_common.TimeDur
