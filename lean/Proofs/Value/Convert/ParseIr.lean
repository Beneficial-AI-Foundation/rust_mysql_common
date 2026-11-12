import Defs

/-! Statements for `struct ParseIr` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `ParseIr::commit`: the converted value. -/
theorem value.convert.ParseIr.commit_eq {T : Type} (x : T) (w : value.Value) : value.convert.ParseIr.commit (x, w) = ok x := by
  rfl

/-- `ParseIr::rollback`: the value it was converted from (every `try_from` producing a `ParseIr`
    stores the original value there, see the `try_from` statements). -/
theorem value.convert.ParseIr.rollback_eq {T : Type} (x : T) (w : value.Value) : value.convert.ParseIr.rollback (x, w) = ok w := by
  rfl

end mysql_common
