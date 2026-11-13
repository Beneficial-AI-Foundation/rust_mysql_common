import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlTimeString
import Proofs.Value.Convert.Time.SignedDurationOps

/-! Statements for `impl TryFrom<Value> for ParseIr<time::Duration>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

namespace TimeDur

/-- The duration of `hours:minutes:seconds.microseconds`, with the sign: total. -/
theorem hmsChain (v : value.Value) (is_neg : Bool) (hours : U32) (minutes seconds : U8)
    (microseconds : U32) :
    ∃ x, (do
        let i ← lift (UScalar.hcast .I64 hours)
        let sd ← value.convert.trusted.time_duration_hours i
        let i1 ← lift (UScalar.hcast .I64 minutes)
        let sd1 ← value.convert.trusted.time_duration_minutes i1
        let sd2 ← value.convert.trusted.time_duration_add sd sd1
        let i2 ← lift (UScalar.hcast .I64 seconds)
        let sd3 ← value.convert.trusted.time_duration_seconds i2
        let sd4 ← value.convert.trusted.time_duration_add sd2 sd3
        let i3 ← lift (UScalar.hcast .I64 microseconds)
        let sd5 ← value.convert.trusted.time_duration_microseconds i3
        let duration ← value.convert.trusted.time_duration_add sd4 sd5
        if is_neg
        then
          let duration1 ← value.convert.trusted.time_duration_neg duration
          ok (core.result.Result.Ok (duration1, v))
        else ok (core.result.Result.Ok (duration, v)) :
        Result (core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration)
          value.convert.FromValueError)) = ok (.Ok (x, v)) ∧
      Trusted.durNanos x =
        timeSignedNanos is_neg 0 hours.val minutes.val seconds.val microseconds.val := by
  have bh : hours.val < 2 ^ 32 := by scalar_tac
  have bm : minutes.val < 2 ^ 8 := by scalar_tac
  have bs : seconds.val < 2 ^ 8 := by scalar_tac
  have bu : microseconds.val < 2 ^ 32 := by scalar_tac
  obtain ⟨sd, hsd, hsdn⟩ := hours_ok (UScalar.hcast .I64 hours) (by rw [u32_hcast_i64_val]; omega)
  obtain ⟨sd1, hsd1, hsd1n⟩ := minutes_ok (UScalar.hcast .I64 minutes)
    (by rw [u8_hcast_i64_val]; omega)
  rw [u32_hcast_i64_val] at hsdn
  rw [u8_hcast_i64_val] at hsd1n
  obtain ⟨sd2, hsd2, hsd2n⟩ := add_ok sd sd1 (by omega)
  obtain ⟨sd3, hsd3, hsd3n⟩ := seconds_ok (UScalar.hcast .I64 seconds)
  rw [u8_hcast_i64_val] at hsd3n
  obtain ⟨sd4, hsd4, hsd4n⟩ := add_ok sd2 sd3 (by omega)
  obtain ⟨sd5, hsd5, hsd5n⟩ := microseconds_ok (UScalar.hcast .I64 microseconds)
  rw [u32_hcast_i64_val] at hsd5n
  obtain ⟨du, hdu, hdun⟩ := add_ok sd4 sd5 (by omega)
  simp only [lift, bind_ok, hsd, hsd1, hsd2, hsd3, hsd4, hsd5, hdu]
  cases is_neg with
  | false =>
    refine ⟨du, by simp, ?_⟩
    simp only [timeSignedNanos, timeNanos, Bool.false_eq_true, ite_false]
    push_cast; omega
  | true =>
    obtain ⟨du1, hdu1, hdu1n⟩ := neg_ok du (by omega)
    refine ⟨du1, by simp [hdu1], ?_⟩
    simp only [timeSignedNanos, timeNanos, ite_true]
    push_cast; omega

/-- The duration of `days hours:minutes:seconds.microseconds`, with the sign: total (`u32` days
    of 86400 seconds are far inside the range of a `time::Duration`). -/
theorem dhmsChain (v : value.Value) (is_neg : Bool) (days : U32) (hours minutes seconds : U8)
    (microseconds : U32) :
    ∃ x, (do
        let i ← lift (UScalar.hcast .I64 days)
        let sd ← value.convert.trusted.time_duration_days i
        let i1 ← lift (UScalar.hcast .I64 hours)
        let sd1 ← value.convert.trusted.time_duration_hours i1
        let sd2 ← value.convert.trusted.time_duration_add sd sd1
        let i2 ← lift (UScalar.hcast .I64 minutes)
        let sd3 ← value.convert.trusted.time_duration_minutes i2
        let sd4 ← value.convert.trusted.time_duration_add sd2 sd3
        let i3 ← lift (UScalar.hcast .I64 seconds)
        let sd5 ← value.convert.trusted.time_duration_seconds i3
        let sd6 ← value.convert.trusted.time_duration_add sd4 sd5
        let i4 ← lift (UScalar.hcast .I64 microseconds)
        let sd7 ← value.convert.trusted.time_duration_microseconds i4
        let duration ← value.convert.trusted.time_duration_add sd6 sd7
        if is_neg
        then
          let duration1 ← value.convert.trusted.time_duration_neg duration
          ok (core.result.Result.Ok (duration1, v))
        else ok (core.result.Result.Ok (duration, v)) :
        Result (core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration)
          value.convert.FromValueError)) = ok (.Ok (x, v)) ∧
      Trusted.durNanos x =
        timeSignedNanos is_neg days.val hours.val minutes.val seconds.val microseconds.val := by
  have bd : days.val < 2 ^ 32 := by scalar_tac
  have bh : hours.val < 2 ^ 8 := by scalar_tac
  have bm : minutes.val < 2 ^ 8 := by scalar_tac
  have bs : seconds.val < 2 ^ 8 := by scalar_tac
  have bu : microseconds.val < 2 ^ 32 := by scalar_tac
  obtain ⟨sd, hsd, hsdn⟩ := days_ok (UScalar.hcast .I64 days) (by rw [u32_hcast_i64_val]; omega)
  obtain ⟨sd1, hsd1, hsd1n⟩ := hours_ok (UScalar.hcast .I64 hours)
    (by rw [u8_hcast_i64_val]; omega)
  rw [u32_hcast_i64_val] at hsdn
  rw [u8_hcast_i64_val] at hsd1n
  obtain ⟨sd2, hsd2, hsd2n⟩ := add_ok sd sd1 (by omega)
  obtain ⟨sd3, hsd3, hsd3n⟩ := minutes_ok (UScalar.hcast .I64 minutes)
    (by rw [u8_hcast_i64_val]; omega)
  rw [u8_hcast_i64_val] at hsd3n
  obtain ⟨sd4, hsd4, hsd4n⟩ := add_ok sd2 sd3 (by omega)
  obtain ⟨sd5, hsd5, hsd5n⟩ := seconds_ok (UScalar.hcast .I64 seconds)
  rw [u8_hcast_i64_val] at hsd5n
  obtain ⟨sd6, hsd6, hsd6n⟩ := add_ok sd4 sd5 (by omega)
  obtain ⟨sd7, hsd7, hsd7n⟩ := microseconds_ok (UScalar.hcast .I64 microseconds)
  rw [u32_hcast_i64_val] at hsd7n
  obtain ⟨du, hdu, hdun⟩ := add_ok sd6 sd7 (by omega)
  simp only [lift, bind_ok, hsd, hsd1, hsd2, hsd3, hsd4, hsd5, hsd6, hsd7, hdu]
  cases is_neg with
  | false =>
    refine ⟨du, by simp, ?_⟩
    simp only [timeSignedNanos, timeNanos, Bool.false_eq_true, ite_false]
    push_cast; omega
  | true =>
    obtain ⟨du1, hdu1, hdu1n⟩ := neg_ok du (by omega)
    refine ⟨du1, by simp [hdu1], ?_⟩
    simp only [timeSignedNanos, timeNanos, ite_true]
    push_cast; omega

end TimeDur

open TimeDur in
/-- `TryFrom<Value> for ParseIr<time::Duration>`: **total and exact** (on ASCII `Bytes`). On a
    `TIME` (any fields: `u32` days cannot overflow a `time::Duration`), or on `Bytes` holding a
    text `TIME` literal, it is `Ok` of the duration with exactly the value's signed nanoseconds
    (`Val.signedDurationNanos`), keeping the original value; on other `Bytes` or any other value
    it is an error carrying the value. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      match (Val.ofValue v).signedDurationNanos with
      | some n => ∃ x, r = .Ok (x, v) ∧ Trusted.durNanos x = n
      | none => r = .Err v ⦄ := by
  cases v with
  | Bytes b =>
    obtain ⟨o, ho, hm⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ (ConvDeps.bytesAscii_bytes ha))
    simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok, Val.ofValue, Val.signedDurationNanos]
    simp only [ConvDeps.vec_deref_val] at hm
    rw [← hm]
    cases o with
    | none => simp
    | some t =>
      obtain ⟨neg, hh, mm, ss, uu⟩ := t
      obtain ⟨x, hx, hxn⟩ := hmsChain (.Bytes b) neg hh mm ss uu
      refine Eq.mpr (congrArg (fun m => WP.spec m _) hx) ?_
      simp only [WP.spec_ok, Option.map_some]
      exact ⟨x, rfl, hxn⟩
  | Time neg dd hh mm ss uu =>
    obtain ⟨x, hx, hxn⟩ := dhmsChain (.Time neg dd hh mm ss uu) neg dd hh mm ss uu
    simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      hx, WP.spec_ok, Val.ofValue, Val.signedDurationNanos]
    exact ⟨x, rfl, hxn⟩
  | _ =>
    simp [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      Val.ofValue, Val.signedDurationNanos]

/-- `TryFrom<Value> for ParseIr<time::Duration>` is an error (no opaque call) on `Bytes` (ASCII)
    that are not a text `TIME` literal and on every value other than `TIME` and `Bytes`. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  cases v with
  | Bytes b =>
    simp only [Val.ofValue] at hv
    obtain ⟨o, ho, hm⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ (ConvDeps.bytesAscii_bytes ha))
    simp only [ConvDeps.vec_deref_val, hv] at hm
    cases o with
    | none =>
      simp [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from, ho]
    | some t => simp at hm
  | Time => simp [Val.ofValue] at hv
  | _ => simp [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- `from_value_opt::<time::Duration>`: as `try_from_spec` of the intermediate, committed:
    **total and exact** (on ASCII `Bytes`). `Ok` of the duration with exactly the value's signed
    nanoseconds for a `TIME` or a text `TIME` literal; otherwise the error carrying the value. -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v ⦃ r =>
      match (Val.ofValue v).signedDurationNanos with
      | some n => ∃ x, r = .Ok x ∧ Trusted.durNanos x = n
      | none => r = .Err v ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) v
    (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha))
  rintro r' ⟨r, hr, rfl⟩
  revert hr
  split <;> intro hr
  · obtain ⟨x, rfl, hx⟩ := hr; exact ⟨x, rfl, hx⟩
  · exact ConvDeps.mapIr_err_of hr

/-- `from_value_opt`: as `try_from_err` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_err (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err v ha hv)]
  rfl

end mysql_common
