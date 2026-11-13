import Defs

/-! Statements for `trait FromRow` (its default `from_row`; spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow::from_row` (the default every impl but `Row`'s uses): when `from_row_opt` is
    `Ok x`, returns `x`. -/
theorem row.convert.FromRow.from_row.default_ok {T : Type} (inst : row.convert.FromRow T) (r : row.Row) (x : T)
    (h : inst.from_row_opt r = ok (.Ok x)) :
    row.convert.FromRow.from_row.default inst r = ok x := by
  sorry

/-- `FromRow::from_row` panics exactly when `from_row_opt` is an `Err`. (The panic message
    differs from upstream, patch 105; the condition is the same.) -/
theorem row.convert.FromRow.from_row.default_panic {T : Type} (inst : row.convert.FromRow T) (r : row.Row)
    (e : row.convert.FromRowError) (h : inst.from_row_opt r = ok (.Err e)) :
    row.convert.FromRow.from_row.default inst r = fail .panic := by
  sorry

end mysql_common
