import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveTime>` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveTime>`: a non-negative (sign flag false) `TIME` with 0 days, or `Bytes` holding a
    non-negative text `TIME` literal (ASCII hypothesis), converts exactly when chrono accepts the
    time; anything else is an error carrying the value. -/
theorem value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveTime.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄ := by
  sorry

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.time.NaiveTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveTime v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).timeOfDayFields with
      | some (h, m, s, us) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoHmsMicroValid h m s us) ∧
        ∀ x, r = .Ok x → chronoTime x = (h, m, s, us * 1000)
      | none => r = .Err v ⦄ := by
  sorry

end mysql_common
