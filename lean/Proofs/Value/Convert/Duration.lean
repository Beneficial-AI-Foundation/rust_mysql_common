import Defs

/-! Statements for `impl FromValue for std::time::Duration` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<Duration>`: a positive `TIME`, or `Bytes` holding a
    non-negative text `TIME` literal, is `Parsed` with that duration (`Val.durationNanos`);
    everything else, including every negative `TIME`, is an error. Hypotheses: the `Bytes` are
    ASCII (see the module docstring: the non-ASCII panic), and a `TIME` has at most 4294967
    microseconds (the `mysql_time_to_duration` overflow, stated separately). -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ n d h m s us, v = .Time n d h m s us → us.val ≤ 4294967) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (fun ir => durNanos (match ir with | .Ready t => t | .Parsed t _ => t)) =
        (Val.ofValue v).durationNanos ∧
      (∀ ir, r = .Ok ir → ∃ t, ir = .Parsed t v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- **Crash path.** `TryFrom<Value> for ParseIrOpt<Duration>` (and so `from_value_opt::<Duration>`)
    fails on a positive `TIME` with more than 4294967 microseconds (the `mysql_time_to_duration`
    overflow). -/
theorem value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_overflow (d : U32) (h m s : U8) (us : U32) (hus : 4294967 < us.val) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from
      (.Time false d h m s us) = fail .integerOverflow := by
  sorry

/-- `from_value_opt::<Duration>`: as `try_from`, committed (same hypotheses). -/
theorem core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ n d h m s us, v = .Time n d h m s us → us.val ≤ 4294967) :
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration v ⦃ r =>
      (okPart r).map durNanos = (Val.ofValue v).durationNanos ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- `From<ParseIrOpt<Duration>> for Value` after `try_from` gives back the original value (every
    successful conversion is `Parsed`). Same hypotheses. -/
theorem value.Value.Insts.CoreConvertFromParseIrOptDuration.recover (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ n d h m s us, v = .Time n d h m s us → us.val ≤ 4294967) :
    (do
      let r ← value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptDuration.from ir
      | .Err e => ok e) = ok v := by
  sorry

end mysql_common
