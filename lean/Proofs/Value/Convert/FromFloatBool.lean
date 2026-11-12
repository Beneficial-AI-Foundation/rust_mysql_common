import Defs

/-! Statements for `impl From<f32>, From<f64>, From<bool> for Value` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<f32> for Value`: `Float`, bit for bit. -/
theorem value.Value.Insts.CoreConvertFromF32.from_eq (x : F32) : value.Value.Insts.CoreConvertFromF32.from x = ok (.Float x) := by
  sorry

/-- Round trip: `from_value_opt::<f32>(Value::from(x)) = Ok(x)`, bit for bit (also for NaNs). -/
theorem value.Value.Insts.CoreConvertFromF32.roundtrip (x : F32) :
    (do let w ← value.Value.Insts.CoreConvertFromF32.from x; value.convert.from_value_opt F32.Insts.Mysql_commonValueConvertFromValueParseIrOptF32 w) = ok (.Ok x) := by
  sorry

/-- `From<f64> for Value`: `Double`, bit for bit. -/
theorem value.Value.Insts.CoreConvertFromF64.from_eq (x : F64) : value.Value.Insts.CoreConvertFromF64.from x = ok (.Double x) := by
  sorry

/-- Round trip: `from_value_opt::<f64>(Value::from(x)) = Ok(x)`, bit for bit. -/
theorem value.Value.Insts.CoreConvertFromF64.roundtrip (x : F64) :
    (do let w ← value.Value.Insts.CoreConvertFromF64.from x; value.convert.from_value_opt F64.Insts.Mysql_commonValueConvertFromValueParseIrOptF64 w) = ok (.Ok x) := by
  sorry

/-- `From<bool> for Value`: `Int 1` or `Int 0`. -/
theorem value.Value.Insts.CoreConvertFromBool.from_spec (x : Bool) :
    value.Value.Insts.CoreConvertFromBool.from x ⦃ w => Val.ofValue w = .int (if x then 1 else 0) ⦄ := by
  sorry

/-- Round trip: `from_value_opt::<bool>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromBool.roundtrip (x : Bool) :
    (do let w ← value.Value.Insts.CoreConvertFromBool.from x; value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool w) = ok (.Ok x) := by
  sorry

end mysql_common
