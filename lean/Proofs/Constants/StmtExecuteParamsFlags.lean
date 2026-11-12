import Defs

/-! Statements for `struct StmtExecuteParamsFlags and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `bits`: the raw value. -/
theorem constants.StmtExecuteParamsFlags.bits_eq (self : constants.StmtExecuteParamsFlags) :
    constants.StmtExecuteParamsFlags.bits self = ok self := by
  sorry

/-- `From<StmtExecuteParamsFlags> for u8`: the raw value. -/
theorem U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from_eq (val : constants.StmtExecuteParamsFlags) :
    U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from val = ok val := by
  sorry

end mysql_common
