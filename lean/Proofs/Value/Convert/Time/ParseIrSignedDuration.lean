import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.ParseMysqlTimeString

/-! Statements for `impl TryFrom<Value> for ParseIr<time::Duration>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- **Crash path.** `TryFrom<Value> for ParseIr<time::Duration>` panics on the `Bytes` on which
    the text parser panics (`Val.timeTextPanics`: a non-ASCII byte, and a fractional regex
    matches): the complement of the hypothesis of `try_from_err`. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = fail .panic := by
  obtain ⟨b, rfl, hb⟩ := ConvDeps.timeTextPanics_bytes hp
  simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.parse_mysql_time_string_panic _ hb, bind_fail]

/-- `TryFrom<Value> for ParseIr<time::Duration>` (partial, glue level: time's `Duration` arithmetic is
    opaque and may panic): on a `TIME`, or on `Bytes` holding a text `TIME` literal, if it
    returns, it returns `Ok` keeping the original value; on any other value (not `TIME`, not
    `Bytes`) it is an error carrying the value. No hypothesis on the `Bytes`: a text `TIME`
    literal is ASCII, and the text parser's panic (`try_from_panic`) is not a return. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (r : core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration) value.convert.FromValueError)
    (h : value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok r) :
    match Val.ofValue v with
    | .time .. => ∃ x, r = .Ok (x, v)
    | .bytes b => (timeStringRead b).isSome → ∃ x, r = .Ok (x, v)
    | _ => r = .Err v := by
  cases v with
  | Bytes b =>
    simp only [Val.ofValue]
    intro hs
    have ha : ¬ timeTextPanics (alloc.vec.Vec.deref b).val := by
      intro hp
      simp only [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
        value.convert.parse_mysql_time_string_panic _ hp, bind_fail] at h
      simp at h
    obtain ⟨o, ho, hm⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ ha)
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

/-- `TryFrom<Value> for ParseIr<time::Duration>` is an error (no opaque call) on `Bytes` that
    are not a text `TIME` literal and on every value other than `TIME` and `Bytes`. Hypothesis:
    the value is not `Bytes` on which the text parser panics (`Val.timeTextPanics`, see
    `try_from_panic`; false of all ASCII `Bytes`). -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  cases v with
  | Bytes b =>
    simp only [Val.ofValue] at hv
    obtain ⟨o, ho, hm⟩ := ConvDeps.spec_eq_ok (value.convert.parse_mysql_time_string_spec _ (ConvDeps.notTimeTextPanics_bytes ha))
    simp only [ConvDeps.vec_deref_val, hv] at hm
    cases o with
    | none =>
      simp [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from, ho]
    | some t => simp at hm
  | Time => simp [Val.ofValue] at hv
  | _ => simp [value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_spec (v : value.Value) (r : core.result.Result time.signed_duration.SignedDuration value.convert.FromValueError)
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
  have hs := value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v r0 h0
  revert hs
  split <;> intro hs
  · obtain ⟨x, rfl⟩ := hs; exact ⟨x, rfl⟩
  · intro hb; obtain ⟨x, rfl⟩ := hs hb; exact ⟨x, rfl⟩
  · exact ConvDeps.mapIr_err_of hs

/-- `from_value_opt`: as `try_from_err` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_err (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err v ha hv)]
  rfl

/-- `TryFrom<Value> for ParseIr<time::Duration>` on `Bytes` with a non-ASCII byte never returns a
    duration: it panics or returns the error carrying the value. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = fail .panic ∨
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b)) := by
  by_cases hp : (Val.ofValue (.Bytes b)).timeTextPanics
  · exact Or.inl (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic _ hp)
  · exact Or.inr (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err _ hp
      (by simpa [Val.ofValue] using timeStringRead_nonascii _ hn))

/-- **Crash path.** `from_value_opt::<time::Duration>` panics on the `Bytes` on which the text
    parser panics (`Val.timeTextPanics`): the complement of the hypothesis of
    `from_value_opt_err`. -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration v = fail .panic :=
  ConvDeps.from_value_opt_fail_of _ rfl v (value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic v hp)

/-- `from_value_opt::<time::Duration>` on `Bytes` with a non-ASCII byte never returns a duration:
    it panics or returns the error carrying the value. -/
theorem time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration.from_value_opt_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Bytes b) = fail .panic ∨
    value.convert.from_value_opt time.signed_duration.SignedDuration.Insts.Mysql_commonValueConvertFromValueParseIrSignedDuration (.Bytes b) = ok (.Err (.Bytes b)) := by
  rcases value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii b hn with h | h
  · exact Or.inl (ConvDeps.from_value_opt_fail_of _ rfl _ h)
  · exact Or.inr (by rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _ h]; rfl)

end mysql_common
