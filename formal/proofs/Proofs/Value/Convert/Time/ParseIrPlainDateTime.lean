import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl TryFrom<Value> for ParseIr<PrimitiveDateTime>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

private theorem create_pdt_spec (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.time.create_primitive_date_time y mo d h mi s us ⦃ o =>
      (o.isSome ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x, o = some x → timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄ := by
  obtain ⟨o, ho, hiff, hm⟩ := ConvDeps.month_from_u8_spec mo
  unfold value.convert.time.create_primitive_date_time
  simp only [ho, bind_ok]
  cases o with
  | none =>
    simp [timeDateValid] at hiff ⊢
    omega
  | some m =>
    have hmn := hm m rfl
    have hy := ConvDeps.u16_hcast_i32_val y
    have hc := Trusted.Date.ofCalendarDate_isSome (UScalar.hcast .I32 y) m d
    simp only [lift, bind_ok, value.convert.trusted.time_date_from_calendar_date]
    have hmr : 1 ≤ mo.val ∧ mo.val ≤ 12 := by rw [← hmn]; cases m <;> simp [Trusted.monthNumber]
    rcases hx : Trusted.Date.ofCalendarDate (UScalar.hcast .I32 y) m d with _ | x
    · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy, hmn] at hc
      simp only [WP.spec_ok, timeDateValid]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies,
        implies_true, and_true]
      exact fun hv => hc hv.1.2.2
    · simp only [hx, Option.isSome_some, true_iff, hy, hmn] at hc
      obtain ⟨h1, h2, h3⟩ := Trusted.Date.ofCalendarDate_some _ _ _ x hx
      obtain ⟨t, ht, htiff, htf⟩ := Trusted.timeFromHmsMicro_spec h mi s us
      simp only [bind_ok, value.convert.trusted.time_time_from_hms_micro, ht]
      cases t with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at htiff
        simp only [WP.spec_ok, Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq,
          false_implies, implies_true, and_true, timeTimeValid]
        exact fun hv => htiff hv.2
      | some t =>
        simp only [Option.isSome_some, true_iff] at htiff
        obtain ⟨t1, t2, t3, t4⟩ := htf t rfl
        simp only [value.convert.trusted.time_primitive_date_time_new, bind_ok, WP.spec_ok,
          Option.isSome_some, true_iff, Option.some.injEq]
        refine ⟨⟨⟨hmr.1, hmr.2, hc⟩, htiff⟩, fun x1 he => ?_⟩
        subst he
        simp [timeDateTime, timeDate, timeTime, Trusted.PrimitiveDateTime.date_new,
          Trusted.PrimitiveDateTime.time_new, h1, h2, h3, hy, hmn, t1, t2, t3, t4]

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on a `Date`: total; converts exactly when
    time accepts the date and the time, to the date-time with these fields. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧
        timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄ := by
  apply WP.spec_bind (create_pdt_spec y mo d h mi s us)
  rintro o ⟨hiff, hf⟩
  cases o with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hiff
    simp only [WP.spec_ok]
    refine ⟨fun _ => trivial, ⟨fun ⟨_, hp⟩ => (by cases hp), fun hv => absurd hv hiff⟩, fun _ _ hp => by cases hp⟩
  | some x =>
    simp only [Option.isSome_some, true_iff] at hiff
    simp only [WP.spec_ok]
    refine ⟨fun h => by simp [okPart] at h, ⟨fun _ => hiff, fun _ => ⟨_, rfl⟩⟩, fun x1 w he => ?_⟩
    cases he
    exact ⟨rfl, hf x rfl⟩

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on `Bytes`: not valid UTF-8 is an error;
    otherwise time's parser (opaque) with the format chosen by the length — more than 19 bytes:
    date-time with fraction; 19: date-time; 10 to 18: date only (which always fails, see
    `..._date_text_rejected`); fewer: an error. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if 19 < b.val.length then Trusted.pdtParseDateTimeMicro (alloc.vec.Vec.deref b)
          else if b.val.length = 19 then Trusted.pdtParseDateTime (alloc.vec.Vec.deref b)
          else if 10 ≤ b.val.length then Trusted.pdtParseDate (alloc.vec.Vec.deref b)
          else .Err (.TryFromParsed .InsufficientInformation)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  simp only [value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.time.parse_mysql_datetime_string_with_time, ConvDeps.str_from_utf8_eq]
  by_cases hu : IsUtf8 b.val
  · simp only [ConvDeps.vec_deref_val, hu, ite_true]
    simp [value.convert.trusted.str_as_bytes, value.convert.trusted.time_parse_insufficient_information,
      value.convert.trusted.time_primitive_date_time_parse_date_time_micro,
      value.convert.trusted.time_primitive_date_time_parse_date_time,
      value.convert.trusted.time_primitive_date_time_parse_date]
    have hl : (b.deref.len = 19#usize) ↔ b.val.length = 19 := by
      constructor
      · intro h; have := congrArg UScalar.val h; simpa [Slice.len] using this
      · intro h; apply UScalar.eq_of_val_eq; simpa [Slice.len] using h
    simp only [hl]
    by_cases h1 : 19 < b.val.length
    · simp only [h1, ite_true, bind_ok]; cases Trusted.pdtParseDateTimeMicro b.deref <;> rfl
    · simp only [h1, ite_false]
      by_cases h2 : b.val.length = 19
      · simp only [h2, ite_true, bind_ok]; cases Trusted.pdtParseDateTime b.deref <;> rfl
      · simp only [h2, ite_false]
        by_cases h3 : 10 ≤ b.val.length
        · simp [h3, Trusted.pdtParseDate]
        · simp [h3]
  · simp [hu, value.convert.trusted.time_parse_insufficient_information]

/-- **Upstream bug.** `TryFrom<Value> for ParseIr<PrimitiveDateTime>` rejects every 10–18 byte
    `Bytes`: a text `DATE` (`"2024-01-31"`) cannot be read as a `PrimitiveDateTime`, because the
    date-only format never yields an hour. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date_text_rejected (b : alloc.vec.Vec U8) (hl : 10 ≤ b.val.length ∧ b.val.length ≤ 18) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b)) := by
  rw [value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes]
  split
  · simp [show ¬ 19 < b.val.length by omega, show b.val.length ≠ 19 by omega, hl.1,
      Trusted.pdtParseDate]
  · rfl

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>`: any other value is an error. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  cases v with
  | Date y mo d h mi s us => exact absurd rfl (hv y mo d h mi s us)
  | Bytes b => exact absurd rfl (hb b)
  | _ => simp [value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- `from_value_opt`: as `try_from_date` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x, r = .Ok x → timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date y mo d h mi s us))
  rintro _ ⟨r, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨ConvDeps.mapIr_okPart h1, ConvDeps.mapIr_isOk h2, ConvDeps.mapIr_ok_of h3⟩

/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if 19 < b.val.length then Trusted.pdtParseDateTimeMicro (alloc.vec.Vec.deref b)
          else if b.val.length = 19 then Trusted.pdtParseDateTime (alloc.vec.Vec.deref b)
          else if 10 ≤ b.val.length then Trusted.pdtParseDate (alloc.vec.Vec.deref b)
          else .Err (.TryFromParsed .InsufficientInformation)) with
        | .Ok x => .Ok x
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes b)]
  split <;> [split <;> simp [ConvDeps.mapIr]; simp [ConvDeps.mapIr]]

/-- `from_value_opt`: as `try_from_date_text_rejected` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_date_text_rejected (b : alloc.vec.Vec U8) (hl : 10 ≤ b.val.length ∧ b.val.length ≤ 18) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime (.Bytes b) = ok (.Err (.Bytes b)) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date_text_rejected b hl)]
  rfl

/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime.from_value_opt_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.plain_date_time.PlainDateTime.Insts.Mysql_commonValueConvertFromValueParseIrPlainDateTime v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other v hv hb)]
  rfl

end mysql_common
