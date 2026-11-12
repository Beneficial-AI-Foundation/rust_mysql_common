import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl FromValue for serde_json::Value` (spec file: `Specs/Value/Json/SerdeIntegration.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<serde_json::Value>`: `Bytes` parsed by `serde_json::from_slice`
    (opaque); anything else is an error carrying the value. The original value is kept. -/
theorem value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Bytes b =>
        match Trusted.jsonFromSlice (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v) := by
  cases v <;> simp [value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.trusted.json_from_slice]
  split <;> simp_all

/-- `From<ParseIr<serde_json::Value>>` for `serde_json::Value` is `commit`, for `Value` is
    `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrValue.from_eq (x : serde_json.value.Value) (w : value.Value) :
    serde_json.value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem serde_json.value.Value.Insts.Mysql_commonValueConvertFromValueParseIrValue.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt serde_json.value.Value.Insts.Mysql_commonValueConvertFromValueParseIrValue v = ok (match v with
      | .Bytes b =>
        match Trusted.jsonFromSlice (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v) := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from_eq]
  cases v <;> simp [serde_json.value.Value.Insts.CoreConvertFromParseIrValue.from,
    value.convert.ParseIr.commit, core.convert.IntoFrom.into]
  case Bytes b => cases Trusted.jsonFromSlice (alloc.vec.Vec.deref b) <;> simp

end mysql_common
