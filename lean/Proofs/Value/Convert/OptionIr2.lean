import Defs

/-! Statements for `enum OptionIr2 and impl FromValue for Option<T>` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for OptionIr2<T>`: `NULL` is `None`. -/
theorem value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_null {T I : Type} (inst : value.convert.FromValue T I) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst .NULL = ok (.Ok .None) := by
  sorry

/-- `TryFrom<Value> for OptionIr2<T>`: any other value is converted by `T`'s intermediate; its
    result is wrapped in `Some`, its error returned unchanged. -/
theorem value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL) (ir : I)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Ok ir)) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst v = ok (.Ok (.Some ir)) := by
  sorry

/-- `TryFrom<Value> for OptionIr2<T>`: errors of `T`'s intermediate are returned unchanged. -/
theorem value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_err {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL)
    (e : value.convert.FromValueError)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Err e)) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst v = ok (.Err e) := by
  sorry

/-- `From<OptionIr2<T>> for Option<T>`: `None`, or `Some` of `T`'s `into`. -/
theorem core.option.Option.Insts.CoreConvertFromOptionIr2.from_eq {T I : Type} (inst : value.convert.FromValue T I) (ir : value.convert.OptionIr2 T I) :
    core.option.Option.Insts.CoreConvertFromOptionIr2.from inst ir =
      match ir with
      | .None => ok none
      | .Some i => inst.coreconvertIntoInst.into i >>= fun t => ok (some t) := by
  sorry

/-- `From<OptionIr2<T>> for Value`: `NULL`, or the rollback of the inner intermediate. -/
theorem value.Value.Insts.CoreConvertFromOptionIr2.from_eq {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into I value.Value)
    (ir : value.convert.OptionIr2 T I) :
    value.Value.Insts.CoreConvertFromOptionIr2.from inst into ir =
      match ir with | .None => ok .NULL | .Some i => into.into i := by
  sorry

/-- `from_value_opt::<Option<T>>`: `NULL` is `Ok(None)`. -/
theorem core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_null {T I : Type} (inst : value.convert.FromValue T I) :
    value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) .NULL = ok (.Ok none) := by
  sorry

/-- `from_value_opt::<Option<T>>`: any other value is `T`'s (default) `from_value_opt`, wrapped in
    `Some` (errors unchanged). -/
theorem core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_some {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL)
    (r : core.result.Result T value.convert.FromValueError)
    (h : value.convert.FromValue.from_value_opt.default inst v = ok r) :
    value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) v =
      ok (match r with | .Ok x => .Ok (some x) | .Err e => .Err e) := by
  sorry

end mysql_common
