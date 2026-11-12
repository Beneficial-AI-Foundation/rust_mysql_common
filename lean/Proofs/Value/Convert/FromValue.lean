import Defs

/-! Statements for `trait FromValue` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `FromValue::from_value` (the default every impl uses): when `from_value_opt` is `Ok x`,
    returns `x`. -/
theorem value.convert.FromValue.from_value.default_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (x : T)
    (h : inst.from_value_opt v = ok (.Ok x)) :
    value.convert.FromValue.from_value.default inst v = ok x := by
  simp [value.convert.FromValue.from_value.default, h]

/-- `FromValue::from_value` panics exactly when `from_value_opt` is an `Err`. (The panic
    message differs from upstream, patch 47; the condition is the same.) -/
theorem value.convert.FromValue.from_value.default_panic {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value)
    (e : value.convert.FromValueError) (h : inst.from_value_opt v = ok (.Err e)) :
    value.convert.FromValue.from_value.default inst v = fail .panic := by
  simp [value.convert.FromValue.from_value.default, h]

/-- `FromValue::from_value_opt` (the default): `try_from` of the intermediate, then `into`; an
    error from `try_from` is returned unchanged. -/
theorem value.convert.FromValue.from_value_opt.default_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (ir : I) (x : T)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Ok ir))
    (hx : inst.coreconvertIntoInst.into ir = ok x) :
    value.convert.FromValue.from_value_opt.default inst v = ok (.Ok x) := by
  simp [value.convert.FromValue.from_value_opt.default, h, hx]

/-- `FromValue::from_value_opt` (the default): an error of `try_from` is returned unchanged. -/
theorem value.convert.FromValue.from_value_opt.default_err {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value)
    (e : value.convert.FromValueError)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Err e)) :
    value.convert.FromValue.from_value_opt.default inst v = ok (.Err e) := by
  simp [value.convert.FromValue.from_value_opt.default, h]

/-- `FromValue::get_intermediate` (the default): `try_from` of the intermediate. -/
theorem value.convert.FromValue.get_intermediate.default_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.FromValue.get_intermediate.default inst v =
      inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v := by
  rfl

end mysql_common
