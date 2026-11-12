import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlDatetimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveDateTime>` (spec file: `Specs/Value/Convert/Chrono.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveDateTime>`: a `Date`, or `Bytes` holding a text
    `DATE`/`DATETIME` literal (ASCII hypothesis), converts exactly when chrono accepts the date
    and the time, to the date-time with these fields, keeping the original value; anything else
    is an error carrying the value. -/
theorem value.convert.ParseIrNaiveDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
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
      (value.convert.parse_mysql_datetime_string_spec _ (ConvDeps.bytesAscii_bytes ha))
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
theorem chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
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

end mysql_common
