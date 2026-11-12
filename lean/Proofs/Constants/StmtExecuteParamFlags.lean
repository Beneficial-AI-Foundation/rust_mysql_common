import Defs

/-! Statements for `struct StmtExecuteParamFlags and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `empty`: no flags. -/
theorem constants.StmtExecuteParamFlags.empty_spec :
    constants.StmtExecuteParamFlags.empty ⦃ r => r.val = 0 ⦄ := by
  sorry

/-- `bits`: the raw value. -/
theorem constants.StmtExecuteParamFlags.bits_eq (self : constants.StmtExecuteParamFlags) :
    constants.StmtExecuteParamFlags.bits self = ok self := by
  sorry

end mysql_common
