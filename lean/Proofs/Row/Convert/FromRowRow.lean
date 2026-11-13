import Defs

/-! Statements for `impl FromRow for Row` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for Row::from_row_opt`: the row itself, always `Ok` (even with taken cells). -/
theorem row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq (r : row.Row) :
    row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_opt r = ok (.Ok r) := by
  rfl

/-- `FromRow for Row::from_row`: the row itself; never panics. -/
theorem row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_eq (r : row.Row) :
    row.Row.Insts.Mysql_commonRowConvertFromRow.from_row r = ok r := by
  rfl

end mysql_common
