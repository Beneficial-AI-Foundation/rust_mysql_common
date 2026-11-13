import Defs

/-! Statements for `impl Index<usize> for Row` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `row[i]`: the value in cell `i`, when it is there. -/
theorem row.Row.Insts.CoreOpsIndexIndexUsizeValue.index_ok (self : row.Row) (index : Usize) (v : value.Value)
    (h : cellAt self.values.val index.val = some v) :
    row.Row.Insts.CoreOpsIndexIndexUsizeValue.index self index = ok v := by
  sorry

/-- `row[i]` panics (`unwrap` on `None`) when the value in cell `i` was taken. -/
theorem row.Row.Insts.CoreOpsIndexIndexUsizeValue.index_taken (self : row.Row) (index : Usize)
    (h : self.values.val[index.val]? = some none) :
    row.Row.Insts.CoreOpsIndexIndexUsizeValue.index self index = fail .panic := by
  sorry

/-- `row[i]` panics (index out of bounds) when there is no cell `i`. -/
theorem row.Row.Insts.CoreOpsIndexIndexUsizeValue.index_oob (self : row.Row) (index : Usize)
    (h : self.values.length ≤ index.val) :
    row.Row.Insts.CoreOpsIndexIndexUsizeValue.index self index = fail .arrayOutOfBounds := by
  sorry

end mysql_common
