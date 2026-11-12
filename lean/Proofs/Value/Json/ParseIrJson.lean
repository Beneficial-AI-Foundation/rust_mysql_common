import Defs

/-! Statements for `impl FromValue for serde_json::Value` (spec file: `Specs/Value/Json/SerdeIntegration.lean`). Proofs: TODO. -/

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
  sorry

/-- `From<ParseIr<serde_json::Value>>` for `serde_json::Value` is `commit`, for `Value` is
    `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrValue.from_eq (x : serde_json.value.Value) (w : value.Value) :
    serde_json.value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok w := by
  sorry

end mysql_common
