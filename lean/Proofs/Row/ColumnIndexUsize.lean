import Defs

/-! Statements for `impl ColumnIndex for usize` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ColumnIndex for usize`: the index itself when there is such a column, otherwise `None`. -/
theorem Usize.Insts.Mysql_commonRowColumnIndex.idx_eq (self : Usize) (columns : Slice packets.Column) :
    Usize.Insts.Mysql_commonRowColumnIndex.idx self columns =
      ok (if self.val < columns.length then some self else none) := by
  sorry

end mysql_common
