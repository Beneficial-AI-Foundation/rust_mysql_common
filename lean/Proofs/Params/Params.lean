import Defs
import Proofs.Util.ParamsAsSql
import Proofs.Defs.LemmasSqlText

/-! Statements for `impl Params` (`into_values`, `into_positional`) (spec file:
`Specs/Params.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open PASUtil

/-- `into_values` of `Params::Empty`: no values, unless the statement has named parameters, in
    which case the first name is reported missing. -/
theorem params.Params.into_values_empty (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values .Empty ns ⦃ r =>
      match ns.map (·.val) with
      | some (n :: _) => ∃ e, r = .Err (.Missing e) ∧ e.val = n.val
      | _ => ∃ v, r = .Ok v ∧ v.val = [] ⦄ := by
  unfold params.Params.into_values
  rcases ns with _ | sl
  · simp
  · cases hs : sl.val with
    | nil => simp [core.slice.Slice.is_empty, Slice.length, hs]
    | cons n l =>
      have hne : ¬ sl.length = 0 := by simp [Slice.length, hs]
      simp only [core.slice.Slice.is_empty, hne, decide_false, Std.bind_ok, Bool.false_eq_true,
        ↓reduceIte]
      step as ⟨v, hv⟩
      simp only [vec_u8_clone_eq, Std.bind_ok, core.convert.IntoFrom.into,
        params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from]
      simp [hs, hv]

/-- `into_values` of `Params::Positional vs`: `vs` unchanged, unless the statement has named
    parameters (`PositionalParamsForNamedQuery`). -/
theorem params.Params.into_values_positional (vs : alloc.vec.Vec value.Value)
    (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values (.Positional vs) ns ⦃ r =>
      match ns.map (·.val) with
      | some (_ :: _) => r = .Err (.Confusion .PositionalParamsForNamedQuery)
      | _ => r = .Ok vs ⦄ := by
  unfold params.Params.into_values
  rcases ns with _ | sl
  · simp
  · cases hs : sl.val with
    | nil => simp [core.slice.Slice.is_empty, Slice.length, hs]
    | cons n l =>
      simp [core.slice.Slice.is_empty, Slice.length, hs, core.convert.IntoFrom.into,
        params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from]

/-- `into_values` of `Params::Named m` for a statement without named parameters (`None` or
    an empty list): `NamedParamsForPositionalQuery`. -/
theorem params.Params.into_values_named_unexpected (m : Trusted.ParamsMap)
    (ns : Option (Slice (alloc.vec.Vec U8))) (h : ∀ s, ns = some s → s.val = []) :
    params.Params.into_values (.Named m) ns ⦃ r =>
      r = .Err (.Confusion .NamedParamsForPositionalQuery) ⦄ := by
  unfold params.Params.into_values
  rcases ns with _ | sl
  · simp [core.convert.IntoFrom.into, params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from]
  · have hs : sl.val = [] := h _ rfl
    simp [core.slice.Slice.is_empty, Slice.length, hs, core.convert.IntoFrom.into,
      params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from]

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
  unfold params.Params.into_positional
  cases p with
  | Empty => simp
  | Named m => exact absurd rfl (hp m)
  | Positional v => simp

/-- `into_positional` of `Params::Named m` when every name has a value: `Positional` with the
    values in the order of the names. -/
theorem params.Params.into_positional_named_ok (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∀ n ∈ ns.val, (Trusted.paramsMapLookup m n.val).isSome) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ v, r = .Ok (.Positional v) ∧
      v.val.map some = ns.val.map (fun n => Trusted.paramsMapLookup m n.val) ⦄ := by
  unfold params.Params.into_positional
  simp only
  have := ip_outer_spec ns m ns.length m (alloc.vec.Vec.new value.Value) 0#usize (by simp) (by simp)
    (by simp) (fun _ _ _ _ => rfl) (by simp)
  refine WP.spec_mono this ?_
  intro r hr
  split at hr
  · obtain ⟨v, rfl, hv⟩ := hr; exact ⟨v, rfl, hv⟩
  · exfalso
    have : (ns.val.find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)) = none := by
      rw [List.find?_eq_none]; intro n hn; have := h n hn; simp only [Option.isNone_iff_eq_none]; intro he; simp [he] at this
    simp [this] at hr

/-- `into_positional` of `Params::Named m` when some name has no value: the **first** such name
    is reported. -/
theorem params.Params.into_positional_named_missing (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∃ n ∈ ns.val, Trusted.paramsMapLookup m n.val = none) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ e, r = .Err e ∧
      (ns.val.find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)).map (·.val) =
        some e.val ⦄ := by
  unfold params.Params.into_positional
  simp only
  have := ip_outer_spec ns m ns.length m (alloc.vec.Vec.new value.Value) 0#usize (by simp) (by simp)
    (by simp) (fun _ _ _ _ => rfl) (by simp)
  refine WP.spec_mono this ?_
  intro r hr
  split at hr
  · exfalso
    obtain ⟨v, -, hv⟩ := hr
    obtain ⟨n, hn, hnone⟩ := h
    have : (none : Option value.Value) ∈ v.val.map some := by
      rw [hv]; exact List.mem_map.mpr ⟨n, hn, hnone⟩
    simp at this
  · exact ⟨_, rfl, by simpa using hr⟩

end mysql_common
