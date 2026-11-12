import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlDatetimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveDate>` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveDate>`: as for `NaiveDateTime`, but only the date fields
    are read and checked (a time part is ignored). -/
theorem value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄ := by
  cases v with
  | Date y mo d h mi s us =>
    obtain ⟨m', hm, hmv⟩ := ConvDeps.u8_into_u32_val mo
    obtain ⟨d', hd, hdv⟩ := ConvDeps.u8_into_u32_val d
    have hy := ConvDeps.u16_hcast_i32_val y
    have hc := Trusted.NaiveDate.ofYmd_isSome (UScalar.hcast .I32 y) m' d'
    simp only [value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
      lift, bind_ok, hm, hd, value.convert.trusted.naive_date_from_ymd,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp only [Val.ofValue, Val.dateTimeFields]
    rcases hx : Trusted.NaiveDate.ofYmd (UScalar.hcast .I32 y) m' d' with _ | x
    · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy, hmv, hdv] at hc
      apply (WP.spec_ok _).mpr
      refine ⟨fun _ => rfl, ⟨fun ⟨_, hp⟩ => (by cases hp), fun hv => absurd hv hc⟩, fun _ _ hp => by cases hp⟩
    · simp only [hx, Option.isSome_some, true_iff, hy, hmv, hdv] at hc
      obtain ⟨h1, h2, h3⟩ := Trusted.NaiveDate.ofYmd_some _ _ _ x hx
      apply (WP.spec_ok _).mpr
      refine ⟨fun h => by simp [okPart] at h, ⟨fun _ => hc, fun _ => ⟨_, rfl⟩⟩, fun x1 w he => ?_⟩
      cases he
      simp [chronoDate, h1, h2, h3, hy, hmv, hdv]
  | Bytes b =>
    have ha' : ∀ c ∈ (alloc.vec.Vec.deref b).val, c.val < 128 := by
      simpa [Val.ofValue, Val.bytesAscii] using ha
    obtain ⟨o, ho, hmo⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_datetime_string_spec _ ha')
    simp only [ConvDeps.vec_deref_val] at hmo
    simp only [value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp only [Val.ofValue, Val.dateTimeFields, ← hmo]
    cases o with
    | none => simp [okPart, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from]
    | some t =>
      obtain ⟨y, mo, d, h, mi, s, us⟩ := t
      have hy31 := ConvDeps.datetimeStringRead_year_lt _ _ hmo.symm
      have hy := ConvDeps.u32_hcast_i32_val y (by simpa using hy31)
      have hc := Trusted.NaiveDate.ofYmd_isSome (UScalar.hcast .I32 y) mo d
      rcases hx : Trusted.NaiveDate.ofYmd (UScalar.hcast .I32 y) mo d with _ | x
      · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy] at hc
        simp [lift, value.convert.trusted.naive_date_from_ymd, hx, okPart, hc]
      · simp only [hx, Option.isSome_some, true_iff, hy] at hc
        obtain ⟨h1, h2, h3⟩ := Trusted.NaiveDate.ofYmd_some _ _ _ x hx
        simp [lift, value.convert.trusted.naive_date_from_ymd, hx, okPart, hc]
        refine ⟨⟨_, rfl⟩, fun x1 w he => ?_⟩
        cases he
        simp [chronoDate, h1, h2, h3, hy]
  | _ =>
    simp [value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
      core.result.Result.Insts.CoreOpsTry.branch, okPart,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, Val.ofValue, Val.dateTimeFields]

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x, r = .Ok x → chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha))
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
