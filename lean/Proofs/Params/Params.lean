import Defs

/-! Statements for `impl Params` (`into_values`, `into_positional`) (spec file:
`Specs/Params.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_values` of `Params::Empty`: no values, unless the statement has named parameters, in
    which case the first name is reported missing. -/
theorem params.Params.into_values_empty (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values .Empty ns ⦃ r =>
      match ns.map (·.val) with
      | some (n :: _) => ∃ e, r = .Err (.Missing e) ∧ e.val = n.val
      | _ => ∃ v, r = .Ok v ∧ v.val = [] ⦄ := by
  sorry

/-- `into_values` of `Params::Positional vs`: `vs` unchanged, unless the statement has named
    parameters (`PositionalParamsForNamedQuery`). -/
theorem params.Params.into_values_positional (vs : alloc.vec.Vec value.Value)
    (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values (.Positional vs) ns ⦃ r =>
      match ns.map (·.val) with
      | some (_ :: _) => r = .Err (.Confusion .PositionalParamsForNamedQuery)
      | _ => r = .Ok vs ⦄ := by
  sorry

/-- `into_values` of `Params::Named m` for a statement without named parameters (`None` or
    an empty list): `NamedParamsForPositionalQuery`. -/
theorem params.Params.into_values_named_unexpected (m : Trusted.ParamsMap)
    (ns : Option (Slice (alloc.vec.Vec U8))) (h : ∀ s, ns = some s → s.val = []) :
    params.Params.into_values (.Named m) ns ⦃ r =>
      r = .Err (.Confusion .NamedParamsForPositionalQuery) ⦄ := by
  sorry

/-- `into_values` of `Params::Named m` when every name of the statement has a value: the values
    in the order of the statement's names (a repeated name gets its value each time). Extra
    entries of the map are ignored. -/
theorem params.Params.into_values_named_ok (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8)) (hne : s.val ≠ [])
    (h : ∀ n ∈ s.val, (Trusted.paramsMapLookup m n.val).isSome) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ v, r = .Ok v ∧
      v.val.map some = s.val.map (fun n => Trusted.paramsMapLookup m n.val) ⦄ := by
  sorry

/-- `into_values` of `Params::Named m` when some name has no value: `Missing` with the name
    `intoValuesMissing` (exact), which is always one of the statement's names without a value. -/
theorem params.Params.into_values_named_missing (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8))
    (h : ∃ n ∈ s.val, Trusted.paramsMapLookup m n.val = none) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ e, r = .Err (.Missing e) ∧
      e.val = intoValuesMissing m (s.val.map (·.val)) ∧
      e.val ∈ s.val.map (·.val) ∧ Trusted.paramsMapLookup m e.val = none ⦄ := by
  sorry

/-- Quirk: with names `[a, b, c]` where only `a` has a value, `into_values` reports `c`, not
    the first missing name `b`. -/
theorem params.Params.into_values_quirk_last (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8)) (a b c : List U8) (hs : s.val.map (·.val) = [a, b, c])
    (ha : (Trusted.paramsMapLookup m a).isSome) (hb : Trusted.paramsMapLookup m b = none)
    (hc : Trusted.paramsMapLookup m c = none) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ e, r = .Err (.Missing e) ∧
      e.val = c ⦄ := by
  sorry

/-- `into_positional` (deprecated) of `Params::Empty` or `Params::Positional`: unchanged (the
    statement's names are not checked, unlike `into_values`). -/
theorem params.Params.into_positional_not_named (p : params.Params)
    (hp : ∀ m, p ≠ .Named m) (ns : Slice (alloc.vec.Vec U8)) :
    params.Params.into_positional p ns ⦃ r => r = .Ok p ⦄ := by
  sorry

/-- `into_positional` of `Params::Named m` when every name has a value: `Positional` with the
    values in the order of the names. -/
theorem params.Params.into_positional_named_ok (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∀ n ∈ ns.val, (Trusted.paramsMapLookup m n.val).isSome) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ v, r = .Ok (.Positional v) ∧
      v.val.map some = ns.val.map (fun n => Trusted.paramsMapLookup m n.val) ⦄ := by
  sorry

/-- `into_positional` of `Params::Named m` when some name has no value: the **first** such name
    is reported. -/
theorem params.Params.into_positional_named_missing (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∃ n ∈ ns.val, Trusted.paramsMapLookup m n.val = none) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ e, r = .Err e ∧
      (ns.val.find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)).map (·.val) =
        some e.val ⦄ := by
  sorry

end mysql_common
