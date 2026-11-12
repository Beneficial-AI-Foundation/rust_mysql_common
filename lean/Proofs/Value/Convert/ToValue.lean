import Defs

/-! Statements for `trait ToValue and impl From<&T> for Value` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `ToValue for T: Into<Value> + Clone`: `self.clone().into()`. -/
theorem value.convert.ToValue.Blanket.to_value_eq {T : Type} (into : core.convert.Into T value.Value) (clone : core.clone.Clone T) (x : T) :
    value.convert.ToValue.Blanket.to_value into clone x = (clone.clone x >>= into.into) := by
  rfl

/-- `From<&T> for Value`: `x.to_value()`. -/
theorem value.Value.Insts.CoreConvertFromSharedAT.from_eq {T : Type} (inst : value.convert.ToValue T) (x : T) :
    value.Value.Insts.CoreConvertFromSharedAT.from inst x = inst.to_value x := by
  rfl

end mysql_common
