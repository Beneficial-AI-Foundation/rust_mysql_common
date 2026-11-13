import Defs

/-! Statements for `const TIMEF_OFS` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TIMEF_OFS` = `0x800000000000` (MySQL's). -/
theorem binlog.misc.TIMEF_OFS_val :
    binlog.misc.TIMEF_OFS.val = 0x800000000000 := by
  simp [binlog.misc.TIMEF_OFS]

end mysql_common
