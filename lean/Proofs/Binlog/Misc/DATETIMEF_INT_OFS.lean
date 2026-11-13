import Defs

/-! Statements for `const DATETIMEF_INT_OFS` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `DATETIMEF_INT_OFS` = `0x8000000000` (MySQL's). -/
theorem binlog.misc.DATETIMEF_INT_OFS_val :
    binlog.misc.DATETIMEF_INT_OFS.val = 0x8000000000 := by
  simp [binlog.misc.DATETIMEF_INT_OFS]

end mysql_common
