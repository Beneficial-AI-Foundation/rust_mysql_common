import Defs

/-! Statements for `enum ParseIrOpt` (spec file: `Specs/Value/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `ParseIrOpt::commit`: the converted value, `Ready` or `Parsed`. -/
theorem value.convert.ParseIrOpt.commit_eq {T : Type} (ir : value.convert.ParseIrOpt T) :
    value.convert.ParseIrOpt.commit ir = ok (match ir with | .Ready t => t | .Parsed t _ => t) := by
  cases ir <;> rfl

/-- `ParseIrOpt::rollback`: for `Parsed`, the stored original value; for `Ready`, `t.into()` —
    which need not be the original value (see `intRecover`). -/
theorem value.convert.ParseIrOpt.rollback_eq {T : Type} (into : core.convert.Into T value.Value) (ir : value.convert.ParseIrOpt T) :
    value.convert.ParseIrOpt.rollback into ir =
      match ir with | .Ready t => into.into t | .Parsed _ w => ok w := by
  cases ir <;> rfl

end mysql_common
