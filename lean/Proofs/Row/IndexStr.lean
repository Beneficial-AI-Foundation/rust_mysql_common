import Defs

/-! Statements for `impl Index<&str> for Row` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `row[name]`: the value in the cell of the first column named exactly `name` (byte for byte,
    case-sensitive), when it is there. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_ok (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i) (v : value.Value)
    (h : cellAt self.values.val i = some v) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = ok v := by
  sorry

/-- `row[name]` panics ("No such column") when no column is named `name`. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_no_column (self : row.Row) (index : Str)
    (hi : colIndexByName index.val self.columns.val = none) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .panic := by
  sorry

/-- `row[name]` panics (`unwrap` on `None`) when the value of the first column named `name` was
    taken. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_taken (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i)
    (h : self.values.val[i]? = some none) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .panic := by
  sorry

/-- `row[name]` panics (index out of bounds) when the column has no cell. (Impossible for rows
    built by the crate, which have one cell per column.) -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_oob (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i)
    (h : self.values.length ≤ i) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .arrayOutOfBounds := by
  sorry

end mysql_common
