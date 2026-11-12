import Defs
import Proofs.Util.ConvBytesTime
import Proofs.Value.Convert.Duration

/-! Statements for `impl From<Duration> for Value` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

namespace mysql_common

/-- `From<Duration> for Value`: the non-negative `TIME` `durationTime` (microseconds rounded half
    up, not carried; days truncated to `u32`). The rounding `(nanos + 500) / 1000` is patch 50's;
    it equals upstream's `(nanos as f64 / 1000.0).round()` for every `nanos < 10^9`. -/
theorem value.Value.Insts.CoreConvertFromDuration.from_spec (d : core.time.Duration) :
    value.Value.Insts.CoreConvertFromDuration.from d ⦃ w =>
      Val.ofValue w = durationTime d.secs.val d.nanos.val ⦄ := by
  have hn := d.nanos_lt
  unfold value.Value.Insts.CoreConvertFromDuration.from value.convert.trusted.duration_as_secs
    value.convert.trusted.duration_subsec_nanos
  step*
  have cast8 : ∀ x : U64, (UScalar.cast UScalarTy.U8 x).val = x.val % 256 := by
    intro x; rw [UScalar.cast_val_eq]; simp [UScalarTy.numBits]
  have cast32 : ∀ x : U64, (UScalar.cast UScalarTy.U32 x).val = x.val % 4294967296 := by
    intro x; rw [UScalar.cast_val_eq]; simp [UScalarTy.numBits]
  have e3 := i3_post ▸ core.convert.num.FromU64U8.from_val_eq seconds
  have e7 := i7_post ▸ core.convert.num.FromU64U8.from_val_eq minutes
  have e12 := i12_post ▸ core.convert.num.FromU64U8.from_val_eq hours
  have es := seconds_post ▸ cast8 i2
  have em := minutes_post ▸ cast8 i6
  have eh := hours_post ▸ cast8 i11
  have ed := i17_post ▸ cast32 i16
  have h4 : i4.val = 3600 := by rw [i4_post]
  have h9 : i9.val = 86400 := by rw [i9_post, h4]
  have h15 : i15.val = 86400 := by rw [i15_post, h4]
  have hs : seconds.val = d.secs.val % 60 := by rw [es, i2_post]; exact Nat.mod_eq_of_lt (by omega)
  have hst1 : secs_total1.val = d.secs.val - d.secs.val % 60 := by rw [secs_total1_post, e3, hs]
  have hm : minutes.val = d.secs.val % 3600 / 60 := by
    rw [em, i6_post, i5_post, h4, hst1, split_a1]; exact Nat.mod_eq_of_lt (by omega)
  have hst2 : secs_total2.val = d.secs.val - d.secs.val % 3600 := by
    rw [secs_total2_post, i8_post, e7, hm, hst1, split_a2]
  have hh : hours.val = d.secs.val % 86400 / 3600 := by
    rw [eh, i11_post, i10_post, h4, h9, hst2, split_a3]; exact Nat.mod_eq_of_lt (by omega)
  have hst3 : secs_total3.val = d.secs.val - d.secs.val % 86400 := by
    rw [secs_total3_post, i14_post, i13_post, e12, hh, hst2, ← split_a4]; ring_nf
  have hd : i17.val = d.secs.val / 86400 % 2 ^ 32 := by
    rw [ed, i16_post, h15, hst3, split_a5]; norm_num
  have hu : micros.val = (d.nanos.val + 500) / 1000 := by rw [micros_post, i1_post]
  simp only [Val.ofValue, durationTime, hd, hh, hm, hs, hu]

/-- Round trip: `from_value_opt::<Duration>(Value::from(d))` is `d` rounded to the nearest
    microsecond (half up), modulo `2^32` days. -/
theorem value.Value.Insts.CoreConvertFromDuration.roundtrip (d : core.time.Duration) :
    (do let w ← value.Value.Insts.CoreConvertFromDuration.from d; value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration w) ⦃ r =>
      ∃ d', r = .Ok d' ∧
        durNanos d' = (d.secs.val % (86400 * 2 ^ 32)) * 10 ^ 9 + (d.nanos.val + 500) / 1000 * 1000 ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromDuration.from_spec d)
  intro w hw
  have hn := d.nanos_lt
  cases w <;> simp only [Val.ofValue, durationTime, reduceCtorEq] at hw
  rename_i neg dd h0 mm ss us
  simp only [Val.time.injEq] at hw
  obtain ⟨rfl, hd, hh, hm, hs, hu⟩ := hw
  apply WP.spec_mono (core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec
    (value.Value.Time false dd h0 mm ss us) (by simp [Val.ofValue, Val.bytesAscii])
    (by rintro _ _ _ _ _ ⟨⟩; omega))
  rintro (d' | e) ⟨h1, h2⟩
  · refine ⟨d', rfl, ?_⟩
    simp only [okPart, Option.map_some, Val.ofValue, Val.durationNanos, Option.some.injEq] at h1
    rw [h1, timeNanos, hd, hh, hm, hs, hu, split_join]
  · simp [okPart, Val.ofValue, Val.durationNanos] at h1

end mysql_common
