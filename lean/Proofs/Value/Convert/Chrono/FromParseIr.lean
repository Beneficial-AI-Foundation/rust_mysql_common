import Defs

/-! Statements for `impl From<ParseIr<_>> for NaiveDateTime, NaiveDate, NaiveTime and for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<ParseIr<NaiveDateTime>>` for `NaiveDateTime` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrNaiveDateTime.from_eq (x : chrono.naive.datetime.NaiveDateTime) (w : value.Value) :
    chrono.naive.datetime.NaiveDateTime.Insts.CoreConvertFromParseIrNaiveDateTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveDateTime.from (x, w) = ok w := by
  sorry

/-- `From<ParseIr<NaiveDate>>` for `NaiveDate` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrNaiveDate.from_eq (x : chrono.naive.date.NaiveDate) (w : value.Value) :
    chrono.naive.date.NaiveDate.Insts.CoreConvertFromParseIrNaiveDate.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveDate.from (x, w) = ok w := by
  sorry

/-- `From<ParseIr<NaiveTime>>` for `NaiveTime` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrNaiveTime.from_eq (x : chrono.naive.time.NaiveTime) (w : value.Value) :
    chrono.naive.time.NaiveTime.Insts.CoreConvertFromParseIrNaiveTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrNaiveTime.from (x, w) = ok w := by
  sorry

end mysql_common
