import Defs

/-! Statements for `impl FromRow for HNil` (spec file: `Specs/Row/Convert/Frunk.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for HNil::from_row_opt`: `Ok(HNil)` for a row with no cells; any other row is
    handed back unchanged as the error. -/
theorem frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq (r : row.Row) :
    frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_opt r =
      ok (if r.values.val = [] then .Ok () else .Err r) := by
  sorry

/-- `FromRow for HNil`: `from_row` is the trait's default (it panics exactly when
    `from_row_opt` is an `Err`, i.e. on a non-empty row). -/
theorem frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_eq :
    frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row =
      row.convert.FromRow.from_row.default frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow := by
  sorry

end mysql_common
