import Defs

/-! Statements for `impl FromValue for Cow<'static, [u8]>` (spec file: `Specs/Value/Convert.lean`).  -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for Cow<'static, [u8]>`: `Owned` bytes of `Bytes`; an error on anything else. -/
theorem alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from v =
      ok (match v with | .Bytes b => .Ok (.Owned b) | _ => .Err v) := by
  cases v <;> rfl

/-- `from_value_opt::<Cow<'static, [u8]>>`: as `try_from`. -/
theorem alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8 v = ok (match v with | .Bytes b => .Ok (.Owned b) | _ => .Err v) := by
  simp only [value.convert.from_value_opt]
  cases v <;> simp [alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from, core.convert.IntoFrom.into, core.convert.FromSame.from]

end mysql_common
