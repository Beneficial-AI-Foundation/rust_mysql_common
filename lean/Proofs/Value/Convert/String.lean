import Defs

/-! Statements for `impl FromValue for String` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for String`: total; succeeds exactly on `Bytes` that are valid UTF-8, with
    the string they encode; on failure the original value (the bytes) is returned. -/
theorem alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- `from_value_opt::<String>`: as `try_from`. -/
theorem alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

end mysql_common
