import Defs
import Proofs.Util.ConvBytesTime
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.MysqlTimeToDuration
import Proofs.Value.Convert.ParseMysqlTimeString

/-! Statements for `impl FromValue for std::time::Duration` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<Duration>`: a non-negative (sign flag false) `TIME`, or `Bytes` holding a
    non-negative text `TIME` literal, is `Parsed` with that duration (`Val.durationNanos`);
    everything else, including every negative `TIME`, is an error. Hypotheses: the value is not
    `Bytes` on which the text parser panics (`Val.timeTextPanics`, stated separately as
    `try_from_panic`; false of all ASCII `Bytes`), and a non-negative `TIME` has at most 4294967
    microseconds (negative ones are rejected before any arithmetic) (the `mysql_time_to_duration` overflow, stated separately). -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (fun ir => durNanos (match ir with | .Ready t => t | .Parsed t _ => t)) =
        (Val.ofValue v).durationNanos ∧
      (∀ ir, r = .Ok ir → ∃ t, ir = .Parsed t v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    simp only [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from]
    have ha' : ¬ timeTextPanics (alloc.vec.Vec.deref b).val := by
      simpa [Val.ofValue, Val.timeTextPanics, vec_deref_val] using ha
    apply WP.spec_bind (value.convert.parse_mysql_time_string_spec _ ha')
    rintro (_ | ⟨neg, hrs, mi, se, us⟩) hr
    · simp only [Option.map_none, vec_deref_val] at hr
      simp only [Val.ofValue, Val.durationNanos]
      simp [okPart]
      rw [← hr]
    · simp only [Option.map_some, vec_deref_val] at hr
      have hus' := timeStringRead_us_lt hr.symm
      cases neg
      · step*
        apply WP.spec_bind (value.convert.mysql_time_to_duration_spec days hours1 mi se us (by omega))
        intro x hx
        have hh : hours1.val = hrs.val % 24 := by
          rw [hours1_post, UScalar.cast_val_eq, i_post]; simp [UScalarTy.numBits]; omega
        simp only [WP.spec_ok, okPart, Option.map_some, Val.ofValue, Val.durationNanos]
        rw [← hr]
        simp only [hx, hh, days_post, timeNanos, Option.some.injEq, core.result.Result.Ok.injEq,
          reduceCtorEq, imp_false]
        exact ⟨by omega, fun ir e => ⟨_, e.symm⟩, not_false⟩
      · simp [okPart, Val.ofValue, Val.durationNanos]
        rw [← hr]
  | Time n d h m s us =>
    cases n
    · simp only [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from]
      have := hus d h m s us rfl
      simp only [Bool.false_eq_true, ite_false]
      apply WP.spec_bind (value.convert.mysql_time_to_duration_spec d h m s us (by omega))
      intro x hx
      simp [okPart, Val.ofValue, Val.durationNanos, hx]
    · simp [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
        okPart, Val.ofValue, Val.durationNanos]
  | _ => simp [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
      okPart, Val.ofValue, Val.durationNanos]

/-- **Crash path.** `TryFrom<Value> for ParseIrOpt<Duration>` (and so `from_value_opt::<Duration>`)
    fails on a non-negative `TIME` with more than 4294967 microseconds (the `mysql_time_to_duration`
    overflow). -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_overflow (d : U32) (h m s : U8) (us : U32) (hus : 4294967 < us.val) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from
      (.Time false d h m s us) = fail .integerOverflow := by
  simp only [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
    Bool.false_eq_true, ite_false]
  rw [value.convert.mysql_time_to_duration_overflow d h m s us (by omega)]
  simp

/-- `from_value_opt::<Duration>`: as `try_from`, committed (same hypotheses; the panic is
    `from_value_opt_panic`). -/
theorem core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration v ⦃ r =>
      (okPart r).map durNanos = (Val.ofValue v).durationNanos ∧ (okPart r = none → r = .Err v) ⦄ := by
  have hs := value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha hus
  simp only [value.convert.from_value_opt]
  apply WP.spec_bind hs
  rintro (ir | e) ⟨h1, h2, h3⟩
  · obtain ⟨t, rfl⟩ := h2 _ rfl
    simpa [core.convert.IntoFrom.into, core.time.Duration.Insts.CoreConvertFromParseIrOptDuration.from,
      value.convert.ParseIrOpt.commit, okPart] using h1
  · simp only [okPart, forall_const] at h3
    cases h3
    simpa [okPart] using h1

/-- `From<ParseIrOpt<Duration>> for Value` after `try_from` gives back the original value (every
    successful conversion is `Parsed`). Same hypotheses. -/
theorem value.Value.Insts.CoreConvertFromParseIrOptDuration.recover (v : value.Value) (ha : ¬ (Val.ofValue v).timeTextPanics)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    (do
      let r ← value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptDuration.from ir
      | .Err e => ok e) = ok v := by
  obtain ⟨r, hr, h1, h2, h3⟩ := spec_exists_ok
    (value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v ha hus)
  rw [hr]
  rcases r with ir | e
  · obtain ⟨t, rfl⟩ := h2 _ rfl
    simp [value.Value.Insts.CoreConvertFromParseIrOptDuration.from, value.convert.ParseIrOpt.rollback]
  · simp only [okPart, forall_const] at h3
    cases h3
    simp

/-- **Crash path.** `TryFrom<Value> for ParseIrOpt<Duration>` panics exactly on the `Bytes` on
    which the text parser panics (`Val.timeTextPanics`: a non-ASCII byte, and a fractional regex
    matches): the complement of the hypothesis of `try_from_spec`. -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = fail .panic := by
  obtain ⟨b, rfl, hb⟩ := ConvDeps.timeTextPanics_bytes hp
  simp only [value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.parse_mysql_time_string_panic _ hb, bind_fail]

/-- `TryFrom<Value> for ParseIrOpt<Duration>` on `Bytes` with a non-ASCII byte never returns a
    duration: it panics or returns the error carrying the value. -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = fail .panic ∨
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (.Err (.Bytes b)) := by
  by_cases hp : (Val.ofValue (.Bytes b)).timeTextPanics
  · exact Or.inl (value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic _ hp)
  · obtain ⟨r, hr, h1, -, h3⟩ := spec_exists_ok
      (value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec _ hp
        (by rintro _ _ _ _ _ ⟨⟩))
    simp only [Val.ofValue, Val.durationNanos, timeStringRead_nonascii _ hn, Option.map_eq_none_iff] at h1
    exact Or.inr (by rw [hr, h3 h1])

/-- **Crash path.** `from_value_opt::<Duration>` panics exactly on the `Bytes` on which the text
    parser panics (`Val.timeTextPanics`): the complement of the hypothesis of
    `from_value_opt_spec`. -/
theorem core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_panic (v : value.Value) (hp : (Val.ofValue v).timeTextPanics) :
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration v = fail .panic := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_panic v hp,
    bind_fail]

/-- `from_value_opt::<Duration>` on `Bytes` with a non-ASCII byte never returns a duration: it
    panics or returns the error carrying the value. -/
theorem core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_nonascii (b : alloc.vec.Vec U8) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration (.Bytes b) = fail .panic ∨
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration (.Bytes b) = ok (.Err (.Bytes b)) := by
  by_cases hp : (Val.ofValue (.Bytes b)).timeTextPanics
  · exact Or.inl (core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_panic _ hp)
  · obtain ⟨r, hr, h1, h3⟩ := spec_exists_ok
      (core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec _ hp
        (by rintro _ _ _ _ _ ⟨⟩))
    simp only [Val.ofValue, Val.durationNanos, timeStringRead_nonascii _ hn, Option.map_eq_none_iff] at h1
    exact Or.inr (by rw [hr, h3 h1])

end mysql_common
