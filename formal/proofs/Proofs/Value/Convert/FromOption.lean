import Defs
import Proofs.Value.Convert.OptionIr2

/-! Statements for `impl From<Option<T>> for Value` (spec file: `Specs/Value/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Option<T>> for Value`: `None` is `NULL`, `Some(x)` is `x.into()`. -/
theorem value.Value.Insts.CoreConvertFromOption.from_eq {T : Type} (into : core.convert.Into T value.Value) (x : Option T) :
    value.Value.Insts.CoreConvertFromOption.from into x =
      match x with | none => ok .NULL | some y => into.into y := by
  cases x <;> rfl

/-- Round trip for `Option<T>`: `None` reads back as `None`. -/
theorem value.Value.Insts.CoreConvertFromOption.roundtrip_none {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into none; value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok none) := by
  simp only [value.Value.Insts.CoreConvertFromOption.from, bind_ok]
  exact core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_null inst

/-- Round trip for `Option<T>`: `Some(x)` reads back as `Some(x)` when `x` round-trips through
    `T` and `Value::from(x)` is not `NULL`. -/
theorem value.Value.Insts.CoreConvertFromOption.roundtrip_some {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value)
    (x : T) (w : value.Value) (hw : into.into x = ok w) (hn : w ≠ .NULL)
    (hx : value.convert.FromValue.from_value_opt.default inst w = ok (.Ok x)) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into (some x); value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok (some x)) := by
  simp only [value.Value.Insts.CoreConvertFromOption.from, hw, bind_ok]
  exact core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_some inst w hn _ hx

/-- **Quirk.** `Some(x)` whose `Value::from(x)` is `NULL` (e.g. `Some(Value::NULL)`,
    `Some(None::<U>)`) reads back as `None`. -/
theorem value.Value.Insts.CoreConvertFromOption.roundtrip_some_null {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value)
    (x : T) (hw : into.into x = ok .NULL) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into (some x); value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok none) := by
  simp only [value.Value.Insts.CoreConvertFromOption.from, hw, bind_ok]
  exact core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_null inst

end mysql_common
