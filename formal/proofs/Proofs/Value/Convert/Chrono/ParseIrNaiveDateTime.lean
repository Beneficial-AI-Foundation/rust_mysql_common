import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlDatetimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveDateTime>` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveDateTime>`: a `Date`, or `Bytes` holding a text
    `DATE`/`DATETIME` literal (hypothesis: not `Bytes` on which the text parser panics, see `try_from_panic`), converts exactly when chrono accepts the date
    and the time, to the date-time with these fields, keeping the original value; anything else
    is an error carrying the value. -/
theorem value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : ¬ (Val.ofValue v).datetimeTextPanics) :
    value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, h, mi, s, us) =>
        ((∃ p, r = .Ok p) ↔
          Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s us) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoDateTime x = (((y : ℤ), mo, d), (h, mi, s, us * 1000))
      | none => r = .Err v ⦄ := by
  cases v with
  | Date y mo d h mi s us =>
    obtain ⟨m', hm, hmv⟩ := ConvDeps.u8_into_u32_val mo
    obtain ⟨d', hd, hdv⟩ := ConvDeps.u8_into_u32_val d
    obtain ⟨h', hh, hhv⟩ := ConvDeps.u8_into_u32_val h
    obtain ⟨mi', hmi, hmiv⟩ := ConvDeps.u8_into_u32_val mi
    obtain ⟨s', hs, hsv⟩ := ConvDeps.u8_into_u32_val s
    have hy := ConvDeps.u16_hcast_i32_val y
    have hc := Trusted.NaiveDate.ofYmd_isSome (UScalar.hcast .I32 y) m' d'
    have ht := Trusted.NaiveTime.ofHmsMicro_isSome h' mi' s' us
    simp only [value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
      lift, bind_ok, hm, hd, hh, hmi, hs, value.convert.trusted.naive_date_from_ymd,
      value.convert.trusted.naive_time_from_hms_micro]
    simp only [Val.ofValue, Val.dateTimeFields]
    rcases hx : Trusted.NaiveDate.ofYmd (UScalar.hcast .I32 y) m' d' with _ | x
    · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy, hmv, hdv] at hc
      simp [okPart, hc]
    · simp only [hx, Option.isSome_some, true_iff, hy, hmv, hdv] at hc
      obtain ⟨h1, h2, h3⟩ := Trusted.NaiveDate.ofYmd_some _ _ _ x hx
      rcases htx : Trusted.NaiveTime.ofHmsMicro h' mi' s' us with _ | t
      · simp only [htx, Option.isSome_none, Bool.false_eq_true, false_iff, hhv, hmiv, hsv] at ht
        simp [okPart, ht]
      · simp only [htx, Option.isSome_some, true_iff, hhv, hmiv, hsv] at ht
        obtain ⟨t1, t2, t3, t4⟩ := Trusted.NaiveTime.ofHmsMicro_some _ _ _ _ t htx
        simp [okPart, hc, ht, value.convert.trusted.naive_datetime_new]
        refine ⟨⟨_, rfl⟩, fun x1 w he => ?_⟩
        cases he
        simp [chronoDateTime, chronoDate, chronoTime, Trusted.NaiveDateTime.date_new,
          Trusted.NaiveDateTime.time_new, h1, h2, h3, hy, hmv, hdv, t1, t2, t3, t4, hhv, hmiv, hsv]
  | Bytes b =>
    obtain ⟨o, ho, hmo⟩ := ConvDeps.spec_eq_ok
      (value.convert.parse_mysql_datetime_string_spec _ (ConvDeps.notDatetimeTextPanics_bytes ha))
    simp only [ConvDeps.vec_deref_val] at hmo
    simp only [value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok]
    simp only [Val.ofValue, Val.dateTimeFields, ← hmo]
    cases o with
    | none => simp [okPart]
    | some t =>
      obtain ⟨y, mo, d, h, mi, s, us⟩ := t
      have hy31 := ConvDeps.datetimeStringRead_year_lt _ _ hmo.symm
      have hy := ConvDeps.u32_hcast_i32_val y (by simpa using hy31)
      have hc := Trusted.NaiveDate.ofYmd_isSome (UScalar.hcast .I32 y) mo d
      have ht := Trusted.NaiveTime.ofHmsMicro_isSome h mi s us
      rcases hx : Trusted.NaiveDate.ofYmd (UScalar.hcast .I32 y) mo d with _ | x
      · simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, hy] at hc
        simp [lift, value.convert.trusted.naive_date_from_ymd, value.convert.trusted.naive_time_from_hms_micro,
          hx, okPart, hc]
      · simp only [hx, Option.isSome_some, true_iff, hy] at hc
        obtain ⟨h1, h2, h3⟩ := Trusted.NaiveDate.ofYmd_some _ _ _ x hx
        rcases htx : Trusted.NaiveTime.ofHmsMicro h mi s us with _ | t
        · simp only [htx, Option.isSome_none, Bool.false_eq_true, false_iff] at ht
          simp [lift, value.convert.trusted.naive_date_from_ymd, value.convert.trusted.naive_time_from_hms_micro,
            hx, htx, okPart, ht]
        · simp only [htx, Option.isSome_some, true_iff] at ht
          obtain ⟨t1, t2, t3, t4⟩ := Trusted.NaiveTime.ofHmsMicro_some _ _ _ _ t htx
          simp [lift, value.convert.trusted.naive_date_from_ymd, value.convert.trusted.naive_time_from_hms_micro,
            hx, htx, okPart, hc, ht, value.convert.trusted.naive_datetime_new]
          refine ⟨⟨_, rfl⟩, fun x1 w he => ?_⟩
          cases he
          simp [chronoDateTime, chronoDate, chronoTime, Trusted.NaiveDateTime.date_new,
            Trusted.NaiveDateTime.time_new, h1, h2, h3, hy, t1, t2, t3, t4]
  | _ =>
    simp [value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
      okPart, Val.ofValue, Val.dateTimeFields]

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_spec (v : value.Value) (ha : ¬ (Val.ofValue v).datetimeTextPanics) :
    value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, h, mi, s, us) =>
        ((∃ p, r = .Ok p) ↔
          Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s us) ∧
        ∀ x, r = .Ok x → chronoDateTime x = (((y : ℤ), mo, d), (h, mi, s, us * 1000))
      | none => r = .Err v ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha))
  rintro _ ⟨r, ⟨h1, h2⟩, rfl⟩
  refine ⟨ConvDeps.mapIr_okPart h1, ?_⟩
  revert h2
  split <;> intro h2
  · exact ⟨ConvDeps.mapIr_isOk h2.1, ConvDeps.mapIr_ok_of h2.2⟩
  · exact ConvDeps.mapIr_err_of h2

/-- **Crash path.** `TryFrom<Value> for ParseIr<NaiveDateTime>` panics exactly on the `Bytes` on which
    the text parser panics (`Val.datetimeTextPanics`: 21–26 bytes, a non-ASCII byte, and the fractional regex matches):
    the complement of the hypothesis of `try_from_spec`. -/
theorem value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_panic (v : value.Value) (hp : (Val.ofValue v).datetimeTextPanics) :
    value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = fail .panic := by
  obtain ⟨b, rfl, hb⟩ := ConvDeps.datetimeTextPanics_bytes hp
  simp only [value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.parse_mysql_datetime_string_panic _ hb, bind_fail]

/-- `TryFrom<Value> for ParseIr<NaiveDateTime>` on `Bytes` with a non-ASCII byte never returns a
    date-time: it panics or returns the error carrying the value. -/
theorem value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = fail .panic ∨
    value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b)) := by
  by_cases hp : (Val.ofValue (.Bytes b)).datetimeTextPanics
  · exact Or.inl (value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_panic _ hp)
  · obtain ⟨r, hr, -, h2⟩ := ConvDeps.spec_eq_ok (value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec _ hp)
    simp only [Val.ofValue, Val.dateTimeFields, datetimeStringRead_nonascii _ hn] at h2
    exact Or.inr (by rw [hr, h2])

/-- **Crash path.** `from_value_opt::<NaiveDateTime>` panics exactly on the `Bytes` on which the text
    parser panics (`Val.datetimeTextPanics`): the complement of the hypothesis of `from_value_opt_spec`. -/
theorem chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_panic (v : value.Value) (hp : (Val.ofValue v).datetimeTextPanics) :
    value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime v = fail .panic :=
  ConvDeps.from_value_opt_fail_of _ rfl v (value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_panic v hp)

/-- `from_value_opt::<NaiveDateTime>` on `Bytes` with a non-ASCII byte never returns a date-time: it
    panics or returns the error carrying the value. -/
theorem chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime (.Bytes b) = fail .panic ∨
    value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime (.Bytes b) = ok (.Err (.Bytes b)) := by
  rcases value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii b hn with h | h
  · exact Or.inl (ConvDeps.from_value_opt_fail_of _ rfl _ h)
  · exact Or.inr (by rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _ h]; rfl)

end mysql_common
