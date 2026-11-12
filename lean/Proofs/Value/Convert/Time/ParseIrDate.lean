import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl TryFrom<Value> for ParseIr<Date>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<Date>` on a `Date`: total; only the date fields are read;
    converts exactly when time accepts them. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧ timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄ := by
  obtain ⟨o, ho, hiff, hm⟩ := ConvDeps.month_from_u8_spec mo
  simp only [value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from, ho, bind_tc_ok]
  cases o with
  | none =>
    simp [okPart, timeDateValid] at hiff ⊢
    omega
  | some m =>
    have hmn := hm m rfl
    have hy := ConvDeps.u16_hcast_i32_val y
    have hc := Trusted.Date.ofCalendarDate_isSome (UScalar.hcast .I32 y) m d
    simp only [lift, bind_tc_ok, value.convert.trusted.time_date_from_calendar_date]
    rcases hx : Trusted.Date.ofCalendarDate (UScalar.hcast .I32 y) m d with _ | x
    · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy, hmn] at hc
      simp only [bind_ok, hx, WP.spec_ok, timeDateValid]
      refine ⟨fun _ => trivial, ⟨fun ⟨_, hp⟩ => (by cases hp), fun hv => absurd hv.2.2 hc⟩,
        fun _ _ hp => by cases hp⟩
    · simp only [hx, Option.isSome_some, true_iff, hy, hmn] at hc
      obtain ⟨h1, h2, h3⟩ := Trusted.Date.ofCalendarDate_some _ _ _ x hx
      simp only [bind_ok, hx, WP.spec_ok, timeDateValid]
      refine ⟨fun h => by simp [okPart] at h, ⟨fun _ => ⟨?_, ?_, hc⟩, fun _ => ⟨_, rfl⟩⟩, fun x1 w he => ?_⟩
      · have := mo.hBounds; rw [← hmn]; cases m <;> simp [Trusted.monthNumber]
      · rw [← hmn]; cases m <;> simp [Trusted.monthNumber]
      · cases he
        simp [timeDate, h1, h2, h3, hy, hmn]

/-- `TryFrom<Value> for ParseIr<Date>` on `Bytes`: time's date parser (opaque) on valid UTF-8. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, .Bytes b)
        | none => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  simp only [value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from,
    ConvDeps.str_from_utf8_eq]
  by_cases hu : IsUtf8 b.val
  · simp only [ConvDeps.vec_deref_val, hu, ite_true]
    simp [value.convert.trusted.time_date_parse_date]
    cases Trusted.dateParseDate b.deref <;> simp
  · simp [hu]

/-- `TryFrom<Value> for ParseIr<Date>`: any other value is an error. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  cases v with
  | Date y mo d h mi s us => exact absurd rfl (hv y mo d h mi s us)
  | Bytes b => exact absurd rfl (hb b)
  | _ => simp [value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- `from_value_opt`: as `try_from_date` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x, r = .Ok x → timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date y mo d h mi s us))
  rintro r' ⟨r, ⟨h1, h2, h3⟩, rfl⟩
  cases r with
  | Ok p =>
    obtain ⟨x, w⟩ := p
    refine ⟨by simp [okPart], ?_, ?_⟩
    · simp only [ConvDeps.mapIr_ok]; exact ⟨fun _ => h2.1 ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · intro x' hx; cases hx; exact (h3 x w rfl).2
  | Err e =>
    have := h1 (by simp [okPart]); cases this
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · simp only [ConvDeps.mapIr_err]; constructor
      · rintro ⟨_, hp⟩; cases hp
      · intro hv; obtain ⟨_, hp⟩ := h2.2 hv; cases hp
    · intro x hx; cases hx

/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes b)]
  split <;> [split <;> simp [ConvDeps.mapIr]; simp [ConvDeps.mapIr]]

/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other v hv hb)]
  rfl

end mysql_common
