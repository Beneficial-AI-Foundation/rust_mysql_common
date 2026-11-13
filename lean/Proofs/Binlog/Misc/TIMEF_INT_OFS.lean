import Defs

/-! Statements for `const TIMEF_INT_OFS` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TIMEF_INT_OFS` = `0x800000` (MySQL's). -/
theorem binlog.misc.TIMEF_INT_OFS_val :
    binlog.misc.TIMEF_INT_OFS.val = 0x800000 := by
  sorry

end mysql_common
