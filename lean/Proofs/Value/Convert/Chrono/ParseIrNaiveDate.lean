import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<NaiveDate>` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<NaiveDate>`: as for `NaiveDateTime`, but only the date fields
    are read and checked (a time part is ignored). -/
theorem value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.ParseIrNaiveDate.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x w, r = .Ok (x, w) → w = v ∧ chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄ := by
  sorry

/-- `from_value_opt`: as `try_from_spec` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) :
    value.convert.from_value_opt chrono.naive.date.NaiveDate.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDate v ⦃ r =>
      (okPart r = none → r = .Err v) ∧
      match (Val.ofValue v).dateTimeFields with
      | some (y, mo, d, _, _, _, _) =>
        ((∃ p, r = .Ok p) ↔ Trusted.chronoYmdValid y mo d) ∧
        ∀ x, r = .Ok x → chronoDate x = ((y : ℤ), mo, d)
      | none => r = .Err v ⦄ := by
  sorry

end mysql_common
