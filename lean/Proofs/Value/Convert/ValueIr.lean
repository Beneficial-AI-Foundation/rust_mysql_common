import Defs

/-! Statements for `struct ValueIr and impl FromValue for Value` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ValueIr`: never fails. -/
theorem value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) : value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Ok v) := by
  rfl

/-- `From<ValueIr> for Value`: the value. -/
theorem value.Value.Insts.CoreConvertFromValueIr.from_eq (v : value.convert.ValueIr) : value.Value.Insts.CoreConvertFromValueIr.from v = ok v := by
  rfl

/-- `from_value_opt::<Value>`: the value itself, always. -/
theorem value.Value.Insts.Mysql_commonValueConvertFromValueValueIr.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt value.Value.Insts.Mysql_commonValueConvertFromValueValueIr v = ok (.Ok v) := by
  simp [value.convert.from_value_opt,
    value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.Value.Insts.CoreConvertFromValueIr.from]

end mysql_common
