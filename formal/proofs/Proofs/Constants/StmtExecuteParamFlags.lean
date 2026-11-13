import Defs

/-! Statements for `struct StmtExecuteParamFlags and its impls` (spec file: `Specs/Constants.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `empty`: no flags. -/
@[step]
theorem constants.StmtExecuteParamFlags.empty_spec :
    constants.StmtExecuteParamFlags.empty ⦃ r => r.val = 0 ⦄ := by
  simp [constants.StmtExecuteParamFlags.empty]

/-- `bits`: the raw value. -/
theorem constants.StmtExecuteParamFlags.bits_eq (self : constants.StmtExecuteParamFlags) :
    constants.StmtExecuteParamFlags.bits self = ok self := by
  rfl

end mysql_common
