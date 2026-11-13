import Defs

/-! Statements for `struct CursorType and its impls` (spec file: `Specs/Constants.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `bits`: the raw value. -/
theorem constants.CursorType.bits_eq (self : constants.CursorType) :
    constants.CursorType.bits self = ok self := by
  rfl

/-- `From<CursorType> for u8`: the raw value. -/
theorem U8.Insts.CoreConvertFromCursorType.from_eq (val : constants.CursorType) :
    U8.Insts.CoreConvertFromCursorType.from val = ok val := by
  rfl

end mysql_common
