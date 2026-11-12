import Defs

/-! Statements for `struct CursorType and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `bits`: the raw value. -/
theorem constants.CursorType.bits_eq (self : constants.CursorType) :
    constants.CursorType.bits self = ok self := by
  sorry

/-- `From<CursorType> for u8`: the raw value. -/
theorem U8.Insts.CoreConvertFromCursorType.from_eq (val : constants.CursorType) :
    U8.Insts.CoreConvertFromCursorType.from val = ok val := by
  sorry

end mysql_common
