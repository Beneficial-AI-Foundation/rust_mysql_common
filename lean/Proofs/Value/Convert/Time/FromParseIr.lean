import Defs

/-! Statements for `impl From<ParseIr<_>> for PrimitiveDateTime, Date, Time, time::Duration and for Value` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<ParseIr<PrimitiveDateTime>>` for `PrimitiveDateTime` is `commit`, for `Value` is
    `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from_eq (x : time.plain_date_time.PlainDateTime) (w : value.Value) :
    time.plain_date_time.PlainDateTime.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrPlainDateTime.from (x, w) = ok w := by
  sorry

/-- `From<ParseIr<Date>>` for `Date` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrDate.from_eq (x : time.date.Date) (w : value.Value) :
    time.date.Date.Insts.CoreConvertFromParseIrDate.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDate.from (x, w) = ok w := by
  sorry

/-- `From<ParseIr<Time>>` for `Time` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrTime.from_eq (x : time.time.Time) (w : value.Value) :
    time.time.Time.Insts.CoreConvertFromParseIrTime.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrTime.from (x, w) = ok w := by
  sorry

/-- `From<ParseIr<time::Duration>>` for `time::Duration` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrSignedDuration.from_eq (x : time.signed_duration.SignedDuration) (w : value.Value) :
    time.signed_duration.SignedDuration.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrSignedDuration.from (x, w) = ok w := by
  sorry

end mysql_common
