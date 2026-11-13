import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlDatetimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveDate>` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveDate>`: as for `NaiveDateTime`, but only the date fields
    are read and checked (a time part is ignored). -/
theorem value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : ¬ (Val.ofValue v).datetimeTextPanics) :
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
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
    obtain ⟨o, ho, hmo⟩ := ConvDeps.spec_eq_ok
      (value.convert.parse_mysql_datetime_string_spec _ (ConvDeps.notDatetimeTextPanics_bytes ha))
    simp only [ConvDeps.vec_deref_val] at hmo
    simp only [value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [Val.ofValue, Val.dateTimeFields, ← hmo]
    cases o with
    | none => simp [okPart]
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, Val.ofValue, Val.dateTimeFields]

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec (v : value.Value) (ha : ¬ (Val.ofValue v).datetimeTextPanics) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x, r = .Ok x → chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha))
  rintro _ ⟨r, ⟨h1, h2⟩, rfl⟩
  refine ⟨ConvDeps.mapIr_okPart h1, ?_⟩
  revert h2
  split <;> intro h2
  · exact ⟨ConvDeps.mapIr_isOk h2.1, ConvDeps.mapIr_ok_of h2.2⟩
  · exact ConvDeps.mapIr_err_of h2

/-- **Crash path.** `TryFrom<Value> for ParseIr<NaiveDate>` panics exactly on the `Bytes` on which
    the text parser panics (`Val.datetimeTextPanics`: 21–26 bytes, a non-ASCII byte, and the fractional regex matches):
    the complement of the hypothesis of `try_from_spec`. -/
theorem value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_panic (v : value.Value) (hp : (Val.ofValue v).datetimeTextPanics) :
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from v = fail .panic := by
  obtain ⟨b, rfl, hb⟩ := ConvDeps.datetimeTextPanics_bytes hp
  simp only [value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.parse_mysql_datetime_string_panic _ hb, bind_fail]

/-- `TryFrom<Value> for ParseIr<NaiveDate>` on `Bytes` with a non-ASCII byte never returns a
    date: it panics or returns the error carrying the value. -/
theorem value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = fail .panic ∨
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b)) := by
  by_cases hp : (Val.ofValue (.Bytes b)).datetimeTextPanics
  · exact Or.inl (value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_panic _ hp)
  · obtain ⟨r, hr, -, h2⟩ := ConvDeps.spec_eq_ok (value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec _ hp)
    simp only [Val.ofValue, Val.dateTimeFields, datetimeStringRead_nonascii _ hn] at h2
    exact Or.inr (by rw [hr, h2])

/-- **Crash path.** `from_value_opt::<NaiveDate>` panics exactly on the `Bytes` on which the text
    parser panics (`Val.datetimeTextPanics`): the complement of the hypothesis of `from_value_opt_spec`. -/
theorem chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_panic (v : value.Value) (hp : (Val.ofValue v).datetimeTextPanics) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate v = fail .panic :=
  ConvDeps.from_value_opt_fail_of _ rfl v (value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_panic v hp)

/-- `from_value_opt::<NaiveDate>` on `Bytes` with a non-ASCII byte never returns a date: it
    panics or returns the error carrying the value. -/
theorem chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate (.Bytes b) = fail .panic ∨
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate (.Bytes b) = ok (.Err (.Bytes b)) := by
  rcases value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii b hn with h | h
  · exact Or.inl (ConvDeps.from_value_opt_fail_of _ rfl _ h)
  · exact Or.inr (by rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _ h]; rfl)

end mysql_common
