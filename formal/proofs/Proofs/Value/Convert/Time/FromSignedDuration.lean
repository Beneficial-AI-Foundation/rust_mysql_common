import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Time.SignedDurationOps
import Proofs.Value.Convert.Time.ParseIrSignedDuration

/-! Statements for `impl From<time::Duration> for Value` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

namespace TimeDur

/-- `From<time::Duration> for Value` after the sign has been taken off. -/
noncomputable def fromTail (negative : Bool) (x1 : time.signed_duration.SignedDuration) : Result value.Value := do
  let i ← value.convert.trusted.time_duration_whole_days x1
  let days ← lift (IScalar.hcast .U32 i)
  let sd ← value.convert.trusted.time_duration_days i
  let x2 ← value.convert.trusted.time_duration_sub x1 sd
  let i1 ← value.convert.trusted.time_duration_whole_hours x2
  let hours ← lift (IScalar.hcast .U8 i1)
  let sd1 ← value.convert.trusted.time_duration_hours i1
  let x3 ← value.convert.trusted.time_duration_sub x2 sd1
  let i2 ← value.convert.trusted.time_duration_whole_minutes x3
  let minutes ← lift (IScalar.hcast .U8 i2)
  let sd2 ← value.convert.trusted.time_duration_minutes i2
  let x4 ← value.convert.trusted.time_duration_sub x3 sd2
  let i3 ← value.convert.trusted.time_duration_whole_seconds x4
  let seconds ← lift (IScalar.hcast .U8 i3)
  let sd3 ← value.convert.trusted.time_duration_seconds i3
  let x5 ← value.convert.trusted.time_duration_sub x4 sd3
  let i4 ← value.convert.trusted.time_duration_whole_microseconds x5
  let microseconds ← lift (IScalar.hcast .U32 i4)
  ok (value.Value.Time negative days hours minutes seconds microseconds)

theorem from_eq (x : time.signed_duration.SignedDuration) :
    value.Value.Insts.CoreConvertFromSignedDuration.from x =
      (do
        let x1 ← if Trusted.durationLtZero x then value.convert.trusted.time_duration_neg x
          else ok x
        fromTail (Trusted.durationLtZero x) x1) := by
  simp only [value.Value.Insts.CoreConvertFromSignedDuration.from,
    value.convert.trusted.time_duration_lt_zero, bind_ok, fromTail]

/-- The split of a non-negative duration into the `TIME` fields: total. -/
theorem fromTail_spec (negative : Bool) (x1 : time.signed_duration.SignedDuration)
    (h0 : 0 ≤ Trusted.durNanos x1) :
    ∃ w, fromTail negative x1 = ok w ∧
      Val.ofValue w =
        .time negative (((Trusted.durNanos x1).toNat / 10 ^ 9 / 86400) % 2 ^ 32)
          (((Trusted.durNanos x1).toNat / 10 ^ 9 % 86400) / 3600)
          (((Trusted.durNanos x1).toNat / 10 ^ 9 % 3600) / 60)
          ((Trusted.durNanos x1).toNat / 10 ^ 9 % 60)
          (((Trusted.durNanos x1).toNat % 10 ^ 9) / 1000) := by
  have hr := durNanos_range x1
  generalize hn1 : Trusted.durNanos x1 = n1 at *
  -- days
  have hi := whole_days_val x1 (by omega)
  obtain ⟨sd, hsd, hsdn⟩ := days_ok (Trusted.durationWholeDays x1) (by omega)
  obtain ⟨x2, hx2, hx2n⟩ := sub_ok x1 sd (by omega) (by omega)
  have h2 : Trusted.durNanos x2 = n1 % (86400 * 10 ^ 9) := by omega
  -- hours
  have hi1 := whole_hours_val x2 (by omega)
  obtain ⟨sd1, hsd1, hsd1n⟩ := hours_ok (Trusted.durationWholeHours x2) (by omega)
  obtain ⟨x3, hx3, hx3n⟩ := sub_ok x2 sd1 (by omega) (by omega)
  have h3 : Trusted.durNanos x3 = n1 % (3600 * 10 ^ 9) := by omega
  -- minutes
  have hi2 := whole_minutes_val x3 (by omega)
  obtain ⟨sd2, hsd2, hsd2n⟩ := minutes_ok (Trusted.durationWholeMinutes x3) (by omega)
  obtain ⟨x4, hx4, hx4n⟩ := sub_ok x3 sd2 (by omega) (by omega)
  have h4 : Trusted.durNanos x4 = n1 % (60 * 10 ^ 9) := by omega
  -- seconds
  have hi3 := whole_seconds_val x4 (by omega)
  obtain ⟨sd3, hsd3, hsd3n⟩ := seconds_ok (Trusted.durationWholeSeconds x4)
  obtain ⟨x5, hx5, hx5n⟩ := sub_ok x4 sd3 (by omega) (by omega)
  have h5 : Trusted.durNanos x5 = n1 % 10 ^ 9 := by omega
  -- microseconds
  have hi4 := whole_microseconds_val x5 (by omega)
  refine ⟨_, by
    simp only [fromTail, value.convert.trusted.time_duration_whole_days,
      value.convert.trusted.time_duration_whole_hours,
      value.convert.trusted.time_duration_whole_minutes,
      value.convert.trusted.time_duration_whole_seconds,
      value.convert.trusted.time_duration_whole_microseconds, lift, bind_ok,
      hsd, hx2, hsd1, hx3, hsd2, hx4, hsd3, hx5]; rfl, ?_⟩
  rw [hn1] at hi; rw [h2] at hi1; rw [h3] at hi2; rw [h4] at hi3; rw [h5] at hi4
  clear hsd hx2 hsd1 hx3 hsd2 hx4 hsd3 hx5 hsdn hsd1n hsd2n hsd3n hx2n hx3n hx4n hx5n h2 h3 h4 h5
  have e32 : UScalarTy.U32.numBits = 32 := rfl
  have e8 : UScalarTy.U8.numBits = 8 := rfl
  simp only [Val.ofValue, IScalar.hcast_val_eq, Val.time.injEq, true_and, hi, hi1, hi2, hi3, hi4,
    e32, e8]
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n1 = (m : Int) := ⟨n1.toNat, by omega⟩
  clear hr h0 hi hi1 hi2 hi3 hi4 hn1
  simp only [Int.toNat_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end TimeDur

open TimeDur in
/-- `From<time::Duration> for Value`, where it returns: every duration above `-2^63` seconds
    becomes the `TIME` `signedDurationTime` of its nanoseconds: the sign flag, and the magnitude
    split into days (mod `2^32`: `whole_days() as u32` wraps), hours, minutes, seconds and
    microseconds (nanoseconds below a microsecond are dropped). -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_spec (x : time.signed_duration.SignedDuration)
    (h : -2 ^ 63 * 10 ^ 9 < Trusted.durNanos x) :
    value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
      Val.ofValue w = signedDurationTime (Trusted.durNanos x) ⦄ := by
  rw [from_eq, Trusted.durationLtZero_spec]
  by_cases hneg : Trusted.durNanos x < 0
  · obtain ⟨x1, hx1, hx1n⟩ := neg_ok x h
    obtain ⟨w, hw, hwv⟩ := fromTail_spec true x1 (by omega)
    simp only [hneg, decide_true, ite_true, hx1, bind_ok, hw, WP.spec_ok, hwv, signedDurationTime,
      Val.time.injEq, true_and]
    rw [hx1n]
    have : (-Trusted.durNanos x).toNat = (Trusted.durNanos x).natAbs := by omega
    simp only [this]; trivial
  · obtain ⟨w, hw, hwv⟩ := fromTail_spec false x (by omega)
    simp only [hneg, decide_false, Bool.false_eq_true, ite_false, bind_ok, hw, WP.spec_ok, hwv,
      signedDurationTime, Val.time.injEq, true_and]
    have : (Trusted.durNanos x).toNat = (Trusted.durNanos x).natAbs := by omega
    simp only [this]; trivial

open TimeDur in
/-- **Upstream panic:** `Value::from` of a `time::Duration` of at most `-2^63` seconds (this
    includes `time::Duration::MIN`) panics: the negation `-x` overflows
    (`checked_neg(..).expect(..)`, signed_duration.rs:1543). Together with `from_spec`: it
    returns iff the duration is above `-2^63` seconds. -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_panic (x : time.signed_duration.SignedDuration)
    (h : Trusted.durNanos x ≤ -2 ^ 63 * 10 ^ 9) :
    value.Value.Insts.CoreConvertFromSignedDuration.from x = fail .panic := by
  rw [from_eq, Trusted.durationLtZero_spec]
  have hneg : Trusted.durNanos x < 0 := by omega
  simp [hneg, neg_panic x h]

open TimeDur in
/-- The panic of `from_panic` is reachable: `time::Duration::seconds(i64::MIN)` is such a
    duration. -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_min_seconds_panics :
    ∃ x, value.convert.trusted.time_duration_seconds (-9223372036854775808)#i64 = ok x ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x = fail .panic := by
  obtain ⟨x, hx, hxn⟩ := seconds_ok (-9223372036854775808)#i64
  exact ⟨x, hx, value.Value.Insts.CoreConvertFromSignedDuration.from_panic x (by rw [hxn]; simp)⟩

open TimeDur in
/-- **The days wrap:** `time::Duration::days(2^32)` is sent as the zero `TIME`
    (`whole_days() as u32` truncates). -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.from_days_wrap :
    ∃ x, value.convert.trusted.time_duration_days 4294967296#i64 = ok x ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
        Val.ofValue w = .time false 0 0 0 0 0 ⦄ := by
  obtain ⟨x, hx, hxn⟩ := days_ok 4294967296#i64 (by simp)
  refine ⟨x, hx, ?_⟩
  have hv : Trusted.durNanos x = 4294967296 * 86400 * 10 ^ 9 := by rw [hxn]; simp
  apply WP.spec_mono (value.Value.Insts.CoreConvertFromSignedDuration.from_spec x (by omega))
  intro w hw
  rw [hw, hv]
  simp [signedDurationTime]

namespace TimeDur

theorem natAbs_timeSignedNanos (neg : Bool) (d h m s us : Nat) :
    (timeSignedNanos neg d h m s us).natAbs = timeNanos d h m s us := by
  cases neg <;> simp [timeSignedNanos]

/-- A `TIME` is the `TIME` of its own nanoseconds iff its fields are normalised and it is not a
    negative zero. -/
theorem signedDurationTime_timeSignedNanos (neg : Bool) (d h m s us : Nat) (hd : d < 2 ^ 32) :
    signedDurationTime (timeSignedNanos neg d h m s us) = .time neg d h m s us ↔
      (h < 24 ∧ m < 60 ∧ s < 60 ∧ us < 10 ^ 6 ∧ (neg = true → timeNanos d h m s us ≠ 0)) := by
  have hsign : (decide (timeSignedNanos neg d h m s us < 0) = neg) ↔
      (neg = true → timeNanos d h m s us ≠ 0) := by
    cases neg <;> simp [timeSignedNanos]
    omega
  simp only [signedDurationTime, natAbs_timeSignedNanos, Val.time.injEq, hsign]
  simp only [timeNanos]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, h1⟩ <;> omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h5, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The nanoseconds of the `TIME` of `n` nanoseconds: `n` with its magnitude taken modulo
    `2^32` days and truncated to microseconds. -/
theorem signedDurationNanos_signedDurationTime (n : Int) :
    (signedDurationTime n).signedDurationNanos =
      some (n.sign * ((n.natAbs % (2 ^ 32 * 86400 * 10 ^ 9) / 1000 * 1000 : ℕ) : ℤ)) := by
  simp only [signedDurationTime, Val.signedDurationNanos, timeSignedNanos, timeNanos,
    Option.some.injEq]
  rcases Int.lt_trichotomy n 0 with hn | hn | hn
  · rw [Int.sign_eq_neg_one_of_neg hn]
    simp only [hn, decide_true, ite_true]
    push_cast; omega
  · subst hn; simp
  · rw [Int.sign_eq_one_of_pos hn]
    have : ¬ n < 0 := by omega
    simp only [this, decide_false, Bool.false_eq_true, ite_false]
    push_cast; omega

end TimeDur

open TimeDur in
/-- Round trip `time::Duration → Value → time::Duration`, for every duration that `Value::from`
    accepts (above `-2^63` seconds): the conversion back succeeds, with the nanoseconds of the
    original's magnitude taken modulo `2^32` days and truncated to microseconds, under the
    original's sign. So the nanoseconds are preserved **iff** the duration is a whole number of
    microseconds and shorter than `2^32` days. (time's `Duration` is opaque: equality is stated
    on `durNanos`.) -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.roundtrip (x : time.signed_duration.SignedDuration)
    (h : -2 ^ 63 * 10 ^ 9 < Trusted.durNanos x) :
    (do let w ← value.Value.Insts.CoreConvertFromSignedDuration.from x; value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration w) ⦃ r =>
      ∃ y, r = .Ok y ∧
        Trusted.durNanos y = (Trusted.durNanos x).sign *
          (((Trusted.durNanos x).natAbs % (2 ^ 32 * 86400 * 10 ^ 9) / 1000 * 1000 : ℕ) : ℤ) ∧
        (Trusted.durNanos y = Trusted.durNanos x ↔
          ((1000 : ℤ) ∣ Trusted.durNanos x ∧
            (Trusted.durNanos x).natAbs < 2 ^ 32 * 86400 * 10 ^ 9)) ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromSignedDuration.from_spec x h)
  intro w hw
  apply WP.spec_mono (time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec w
    (by rw [hw]; simp [signedDurationTime, Val.timeTextPanics]))
  intro r hr
  rw [hw, signedDurationNanos_signedDurationTime] at hr
  obtain ⟨y, rfl, hy⟩ := hr
  refine ⟨y, rfl, hy, ?_⟩
  rw [hy]
  generalize Trusted.durNanos x = n
  rcases Int.lt_trichotomy n 0 with hn | hn | hn
  · rw [Int.sign_eq_neg_one_of_neg hn]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega
  · subst hn; simp
  · rw [Int.sign_eq_one_of_pos hn]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.natAbs, by omega⟩
    simp only [Int.natAbs_natCast]
    omega

open TimeDur in
/-- Round trip `Value → time::Duration → Value`, for every `TIME`: both conversions succeed, and
    the result is the original `TIME` **iff** its fields are normalised (hours `< 24`, minutes
    and seconds `< 60`, microseconds `< 10^6`) and it is not a negative zero. (Otherwise the
    result is the normalised `TIME`, `signedDurationTime` of the same nanoseconds, whose days
    can wrap: `Time(false, 4294967295, 24, 0, 0, 0)` is `2^32` days and comes back with 0 days.
    The days never wrap when the fields are normalised.) -/
theorem value.Value.Insts.CoreConvertFromSignedDuration.roundtrip_value (neg : Bool) (d : U32) (h m s : U8) (us : U32) :
    ∃ x, value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Time neg d h m s us) = ok (.Ok x) ∧
      value.Value.Insts.CoreConvertFromSignedDuration.from x ⦃ w =>
        Val.ofValue w = signedDurationTime (timeSignedNanos neg d.val h.val m.val s.val us.val) ∧
        (w = .Time neg d h m s us ↔
          (h.val < 24 ∧ m.val < 60 ∧ s.val < 60 ∧ us.val < 10 ^ 6 ∧
            (neg = true → timeNanos d.val h.val m.val s.val us.val ≠ 0))) ⦄ := by
  obtain ⟨r, hr, hp⟩ := ConvDeps.spec_eq_ok
    (time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec
      (.Time neg d h m s us) (by simp [Val.ofValue, Val.timeTextPanics]))
  simp only [Val.ofValue, Val.signedDurationNanos] at hp
  obtain ⟨x, rfl, hx⟩ := hp
  refine ⟨x, hr, ?_⟩
  have bd : d.val < 2 ^ 32 := by scalar_tac
  have bh : h.val < 2 ^ 8 := by scalar_tac
  have bm : m.val < 2 ^ 8 := by scalar_tac
  have bs : s.val < 2 ^ 8 := by scalar_tac
  have bu : us.val < 2 ^ 32 := by scalar_tac
  apply WP.spec_mono (value.Value.Insts.CoreConvertFromSignedDuration.from_spec x (by
    rw [hx]; simp only [timeSignedNanos, timeNanos]; split <;> push_cast <;> omega))
  intro w hw
  rw [hx] at hw
  refine ⟨hw, ?_⟩
  rw [← signedDurationTime_timeSignedNanos neg d.val h.val m.val s.val us.val bd, ← hw]
  constructor
  · rintro rfl; rfl
  · intro he
    cases w <;> simp only [Val.ofValue, reduceCtorEq, Val.time.injEq] at he
    obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := he
    simp only [value.Value.Time.injEq, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac

end mysql_common
