import Defs

/-! Statements for `fn new_row` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new_row`: the row of the given values (every cell present) and columns, when there are as
    many of each. -/
theorem row.new_row_spec (values : alloc.vec.Vec value.Value) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length = columns.length) :
    row.new_row values columns ⦃ r => r.values.val = values.val.map some ∧ r.columns = columns ⦄ := by
  sorry

/-- `new_row` panics (`assert!`) when the numbers of values and columns differ. -/
theorem row.new_row_panics (values : alloc.vec.Vec value.Value) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length ≠ columns.length) :
    row.new_row values columns = fail .assertionFailure := by
  sorry

end mysql_common
