import Defs

/-! Statements for `impl ColumnIndex for &str` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ColumnIndex for &str`: the position of the first column named exactly `self` (byte for
    byte, case-sensitive), or `None`. Never panics. -/
theorem Shared0Str.Insts.Mysql_commonRowColumnIndex.idx_spec (self : Str) (columns : Slice packets.Column) :
    Shared0Str.Insts.Mysql_commonRowColumnIndex.idx self columns ⦃ o =>
      o.map (·.val) = colIndexByName self.val columns.val ⦄ := by
  sorry

end mysql_common
