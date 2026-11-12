import Defs

/-! Statements for `fn from_value, fn from_value_opt` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `from_value::<T>(v)`: `T::from_value(v)`. -/
theorem value.convert.from_value_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.from_value inst v = inst.from_value v := by
  sorry

/-- `from_value_opt::<T>(v)`: `T::from_value_opt(v)`. -/
theorem value.convert.from_value_opt_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.from_value_opt inst v = inst.from_value_opt v := by
  sorry

end mysql_common
