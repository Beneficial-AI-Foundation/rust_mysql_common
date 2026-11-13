import Defs

/-! Statements for `fn from_row` and `fn from_row_opt` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `from_row`: the impl's `FromRow::from_row`. -/
theorem row.convert.from_row_eq {T : Type} (inst : row.convert.FromRow T) (r : row.Row) :
    row.convert.from_row inst r = inst.from_row r := by
  sorry

/-- `from_row_opt`: the impl's `FromRow::from_row_opt`. -/
theorem row.convert.from_row_opt_eq {T : Type} (inst : row.convert.FromRow T) (r : row.Row) :
    row.convert.from_row_opt inst r = inst.from_row_opt r := by
  sorry

end mysql_common
