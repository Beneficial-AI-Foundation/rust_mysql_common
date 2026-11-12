import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlTimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<time::Duration>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<time::Duration>` (partial, glue level: time's `Duration` arithmetic is
    opaque and may panic): on a `TIME`, or on `Bytes` (ASCII) holding a text `TIME` literal, if it
    returns, it returns `Ok` keeping the original value; on other `Bytes` or any other value it
    is an error carrying the value. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) (r : core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration) value.convert.FromValueError)
    (h : value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok r) :
    match Val.ofValue v with
    | .time .. => ∃ x, r = .Ok (x, v)
    | .bytes b => (timeStringRead b).isSome → ∃ x, r = .Ok (x, v)
    | _ => r = .Err v := by
  cases v with
  | Bytes b =>
    simp only [Val.ofValue]
    intro hs
    obtain ⟨o, ho, hm⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ (ConvDeps.bytesAscii_bytes ha))
    simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ho, bind_ok] at h
    cases o with
    | none =>
      simp only [ConvDeps.vec_deref_val, Option.map_none] at hm
      rw [← hm] at hs; simp at hs
    | some t =>
      obtain ⟨neg, hh, mm, ss, uu⟩ := t
      simp only at h
      repeat (obtain ⟨_, _, h⟩ := ConvDeps.bind_eq_ok_inv h)
      split at h <;> (repeat (obtain ⟨_, _, h⟩ := ConvDeps.bind_eq_ok_inv h)) <;>
        (simp only [ok.injEq] at h; exact ⟨_, h.symm⟩)
  | Time neg dd hh mm ss uu =>
    simp only [Val.ofValue]
    simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from] at h
    repeat (obtain ⟨_, _, h⟩ := ConvDeps.bind_eq_ok_inv h)
    split at h <;> (repeat (obtain ⟨_, _, h⟩ := ConvDeps.bind_eq_ok_inv h)) <;>
      (simp only [ok.injEq] at h; exact ⟨_, h.symm⟩)
  | _ =>
    simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      ok.injEq] at h
    simp [Val.ofValue, h]

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

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) (r : core.result.Result time.signed_duration.SignedDuration value.convert.FromValueError)
    (h : value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = ok r) :
    match Val.ofValue v with
    | .time .. => ∃ x, r = .Ok x
    | .bytes b => (timeStringRead b).isSome → ∃ x, r = .Ok x
    | _ => r = .Err v := by
  have hsave := h
  simp only [value.convert.from_value_opt] at h
  obtain ⟨r0, h0, -⟩ := ConvDeps.bind_eq_ok_inv h
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _ h0, ok.injEq] at hsave
  subst hsave
  have hs := value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha r0 h0
  revert hs
  split <;> intro hs
  · obtain ⟨x, rfl⟩ := hs; exact ⟨x, rfl⟩
  · intro hb; obtain ⟨x, rfl⟩ := hs hb; exact ⟨x, rfl⟩
  · exact ConvDeps.mapIr_err_of hs

/-- `from_value_opt`: as `try_from_err` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_err (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err v ha hv)]
  rfl

end mysql_common
