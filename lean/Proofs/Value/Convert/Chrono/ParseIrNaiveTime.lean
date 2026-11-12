import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlTimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveTime>` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveTime>`: a non-negative (sign flag false) `TIME` with 0 days, or `Bytes` holding a
    non-negative text `TIME` literal (ASCII hypothesis), converts exactly when chrono accepts the
    time; anything else is an error carrying the value. -/
theorem value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄ := by
  cases v with
  | Time neg i h m s us =>
    cases neg
    · by_cases hi : i = 0#u32
      · subst hi
        obtain ⟨h', hh, hhv⟩ := ConvDeps.u8_into_u32_val h
        obtain ⟨m', hm, hmv⟩ := ConvDeps.u8_into_u32_val m
        obtain ⟨s', hs, hsv⟩ := ConvDeps.u8_into_u32_val s
        have ht := Trusted.NaiveTime.ofHmsMicro_isSome h' m' s' us
        simp only [value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
          Bool.false_eq_true, ite_false]
        split
        · simp only [bind_ok, hh, hm, hs, value.convert.trusted.naive_time_from_hms_micro]
          rcases htx : Trusted.NaiveTime.ofHmsMicro h' m' s' us with _ | t
          · simp only [htx, Option.isSome_none, Bool.false_eq_true, false_iff, hhv, hmv, hsv] at ht
            simp [okPart, ht, core.result.Result.Insts.CoreOpsTry.branch, Val.ofValue, Val.timeOfDayFields]
          · simp only [htx, Option.isSome_some, true_iff, hhv, hmv, hsv] at ht
            obtain ⟨t1, t2, t3, t4⟩ := Trusted.NaiveTime.ofHmsMicro_some _ _ _ _ t htx
            simp [okPart, ht, core.result.Result.Insts.CoreOpsTry.branch, Val.ofValue, Val.timeOfDayFields]
            refine ⟨⟨_, rfl⟩, fun x1 w he => ?_⟩
            cases he
            simp [chronoTime, t1, t2, t3, t4, hhv, hmv, hsv]
        · exact absurd rfl (by assumption)
      · simp only [value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
          Bool.false_eq_true, ite_false]
        have hi' : i.val ≠ 0 := fun h0 => hi (UScalar.eq_of_val_eq (by simpa using h0))
        split
        · exact absurd rfl hi
        · simp [okPart, core.result.Result.Insts.CoreOpsTry.branch, Val.ofValue, Val.timeOfDayFields, hi',
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            core.convert.FromSame.from]
    · simp [value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
        okPart, core.result.Result.Insts.CoreOpsTry.branch, Val.ofValue, Val.timeOfDayFields,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from]
  | Bytes b =>
    have ha' : ∀ c ∈ (alloc.vec.Vec.deref b).val, c.val < 128 := by
      simpa [Val.ofValue, Val.bytesAscii] using ha
    obtain ⟨o, ho, hmo⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ ha')
    simp only [ConvDeps.vec_deref_val] at hmo
    simp only [value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok]
    simp only [Val.ofValue, Val.timeOfDayFields, ← hmo]
    cases o with
    | none => simp [okPart, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from]
    | some t =>
      obtain ⟨neg, h, m, s, us⟩ := t
      cases neg
      · obtain ⟨m', hm, hmv⟩ := ConvDeps.spec_eq_ok (UScalar.cast_inBounds_spec .U32 m (by scalar_tac))
        obtain ⟨s', hs, hsv⟩ := ConvDeps.spec_eq_ok (UScalar.cast_inBounds_spec .U32 s (by scalar_tac))
        have ht := Trusted.NaiveTime.ofHmsMicro_isSome h m' s' us
        rcases htx : Trusted.NaiveTime.ofHmsMicro h m' s' us with _ | t
        · simp only [htx, Option.isSome_none, Bool.false_eq_true, false_iff, hmv, hsv] at ht
          simp [okPart, hm, hs, value.convert.trusted.naive_time_from_hms_micro, htx, ht,
            core.result.Result.Insts.CoreOpsTry.branch]
        · simp only [htx, Option.isSome_some, true_iff, hmv, hsv] at ht
          obtain ⟨t1, t2, t3, t4⟩ := Trusted.NaiveTime.ofHmsMicro_some _ _ _ _ t htx
          simp [okPart, hm, hs, value.convert.trusted.naive_time_from_hms_micro, htx, ht,
            core.result.Result.Insts.CoreOpsTry.branch]
          refine ⟨⟨_, rfl⟩, fun x1 w he => ?_⟩
          cases he
          simp [chronoTime, t1, t2, t3, t4, hmv, hsv]
      · simp [okPart, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.FromSame.from]
  | _ =>
    simp [value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
      core.result.Result.Insts.CoreOpsTry.branch, okPart, Val.ofValue, Val.timeOfDayFields,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x, r = .Ok x → chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha))
  rintro r' ⟨r, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun h => ?_, ?_⟩
  · cases r with
    | Ok p => simp [okPart, ConvDeps.mapIr] at h
    | Err e => rw [h1 rfl]; rfl
  · split
    · rename_i heq; rw [heq] at h2; obtain ⟨h2, h3⟩ := h2
      refine ⟨?_, ?_⟩
      · rw [← h2]; cases r with
        | Ok p => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
        | Err e => exact ⟨fun ⟨_, hp⟩ => (by cases hp), fun ⟨_, hp⟩ => (by cases hp)⟩
      · intro x hx
        cases r with
        | Ok p => obtain ⟨x0, w⟩ := p; cases hx; exact (h3 x0 w rfl).2
        | Err e => cases hx
    · rename_i heq; rw [heq] at h2; rw [h2]; rfl

end mysql_common
