import Defs

/-! Statements for `impl FromValue for Vec<u8>` (spec file: `Specs/Value/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for Vec<u8>`: the bytes of `Bytes`; an error on anything else (no
    conversion of numbers to text). -/
theorem alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with | .Bytes b => .Ok b | _ => .Err v) := by
  cases v <;> rfl

/-- `from_value_opt::<Vec<u8>>`: as `try_from`. -/
theorem alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8 v = ok (match v with | .Bytes b => .Ok b | _ => .Err v) := by
  simp only [value.convert.from_value_opt]
  cases v <;> simp [alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from, core.convert.IntoFrom.into, core.convert.FromSame.from]

end mysql_common
