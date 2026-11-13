import Defs

/-! Statements for `trait FromRow` (its default `from_row`; spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow::from_row` (the default every impl but `Row`'s uses): `x` when `from_row_opt` is
    `Ok x`, a panic exactly when it is an `Err`. (The panic message differs from upstream, patch
    105; the condition is the same.) -/
theorem row.convert.FromRow.from_row.default_eq {T : Type} (inst : row.convert.FromRow T) (r : row.Row) :
    row.convert.FromRow.from_row.default inst r =
      (inst.from_row_opt r >>= fun res => match res with
        | .Ok x => ok x
        | .Err _ => fail .panic) := by
  sorry

end mysql_common
