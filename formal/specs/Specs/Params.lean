import Proofs.Params.ParamsError
import Proofs.Params.Params
import Proofs.Params.FromImpls
import Proofs.Params.FromTuples

/-!
# `src/params.rs`
    `Params::into_values`, `Params::into_positional` (deprecated), the `From` impls into
    `ParamsError` and into `Params` (`&T`, `Vec<T>`, `Vec<(N, V)>`, `()`, the twelve tuples).
    Patches 87–91: the `HashMap` goes through `sql_trusted` (patch 80), the loops become index
    loops, `sort_unstable` an in-crate insertion sort, the redefinition panic loses its
    message, `From` impls are selected with `#[verify::start_from]`.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/SqlText.lean` §2 (`intoValuesMissing`); `Trusted.paramsMapLookup`
    and `Trusted.paramsMapEntries` (`FunsExternal.lean`) for the map of `Params::Named`.

    **Trusted axioms:** the `HashMap` model of `FunsExternal.lean` (the `sql_trusted.params_map_*`
    helpers): `Trusted.paramsMapEntries`, `paramsMapEntries_keys_nodup`,
    `paramsMapEntries_length`, and for `From<Vec<(N, V)>>`
    `paramsMapEmpty`/`paramsMapEntries_empty`/`paramsMapInsert`/`paramsMapEntries_insert` (whose
    room-below-`usize::MAX` hypothesis follows from the input `Vec`'s length bound, so no extra
    hypothesis is needed), for `into_positional` `paramsMapRemove`/`paramsMapEntries_remove`. Respecting the model's limit,
    no statement mentions the iteration order: maps are described by lookups or by their
    entries up to `List.Perm`.

    **What is stated.** Exact results for every variant and every input (none panics, except
    `From<Vec<(N, V)>>` on a repeated name). Generic `From` impls are stated assuming the element
    conversions return (`= ok`), which is the weakest precondition for a non-panicking result.

    **Behaviour to note.**
    - Quirk (`into_values_quirk_last`): when a name has no value, `into_values` reports the first
      such name only if some later name has a value; otherwise it reports the **last** name
      (also missing, but not the first). `into_positional` reports the first.
    - Extra map entries are ignored; a repeated name receives the same value at each position.
    - `into_positional` returns `Empty`/`Positional` unchanged even when the statement has named
      parameters (`into_values` reports `Missing` / `PositionalParamsForNamedQuery`).

    **Not covered:** `From<&[&dyn ToValue]>` (trait objects are not translated), `Debug for
    Params`, derived `PartialEq`/`Clone`, the `Display` of the errors.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl From<MissingNamedParameterError>/<ParamsConfusionError> for ParamsError` -/

/-- `From<MissingNamedParameterError> for ParamsError`: `ParamsError::Missing`. -/
recall params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from_eq
    (e : params.MissingNamedParameterError) :
    params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from e =
      ok (.Missing e)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from_eq
/-- `From<ParamsConfusionError> for ParamsError`: `ParamsError::Confusion`. -/
recall params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from_eq
    (e : params.ParamsConfusionError) :
    params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from e = ok (.Confusion e)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from_eq
/-! ### `impl Params` -/

/-- `into_values` of `Params::Empty`: no values, unless the statement has named parameters, in
    which case the first name is reported missing. -/
recall params.Params.into_values_empty (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values .Empty ns ⦃ r =>
      match ns.map (·.val) with
      | some (n :: _) => ∃ e, r = .Err (.Missing e) ∧ e.val = n.val
      | _ => ∃ v, r = .Ok v ∧ v.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_empty
/-- `into_values` of `Params::Positional vs`: `vs` unchanged, unless the statement has named
    parameters (`PositionalParamsForNamedQuery`). -/
recall params.Params.into_values_positional (vs : alloc.vec.Vec value.Value)
    (ns : Option (Slice (alloc.vec.Vec U8))) :
    params.Params.into_values (.Positional vs) ns ⦃ r =>
      match ns.map (·.val) with
      | some (_ :: _) => r = .Err (.Confusion .PositionalParamsForNamedQuery)
      | _ => r = .Ok vs ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_positional
/-- `into_values` of `Params::Named m` for a statement without named parameters (`None` or
    an empty list): `NamedParamsForPositionalQuery`. -/
recall params.Params.into_values_named_unexpected (m : Trusted.ParamsMap)
    (ns : Option (Slice (alloc.vec.Vec U8))) (h : ∀ s, ns = some s → s.val = []) :
    params.Params.into_values (.Named m) ns ⦃ r =>
      r = .Err (.Confusion .NamedParamsForPositionalQuery) ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_named_unexpected
/-- `into_values` of `Params::Named m` when every name of the statement has a value: the values
    in the order of the statement's names (a repeated name gets its value each time). Extra
    entries of the map are ignored. -/
recall params.Params.into_values_named_ok (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8)) (hne : s.val ≠ [])
    (h : ∀ n ∈ s.val, (Trusted.paramsMapLookup m n.val).isSome) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ v, r = .Ok v ∧
      v.val.map some = s.val.map (fun n => Trusted.paramsMapLookup m n.val) ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_named_ok
/-- `into_values` of `Params::Named m` when some name has no value: `Missing` with the name
    `intoValuesMissing` (exact), which is always one of the statement's names without a value. -/
recall params.Params.into_values_named_missing (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8))
    (h : ∃ n ∈ s.val, Trusted.paramsMapLookup m n.val = none) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ e, r = .Err (.Missing e) ∧
      e.val = intoValuesMissing m (s.val.map (·.val)) ∧
      e.val ∈ s.val.map (·.val) ∧ Trusted.paramsMapLookup m e.val = none ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_named_missing
/-- Quirk: with names `[a, b, c]` where only `a` has a value, `into_values` reports `c`, not
    the first missing name `b`. -/
recall params.Params.into_values_quirk_last (m : Trusted.ParamsMap)
    (s : Slice (alloc.vec.Vec U8)) (a b c : List U8) (hs : s.val.map (·.val) = [a, b, c])
    (ha : (Trusted.paramsMapLookup m a).isSome) (hb : Trusted.paramsMapLookup m b = none)
    (hc : Trusted.paramsMapLookup m c = none) :
    params.Params.into_values (.Named m) (some s) ⦃ r => ∃ e, r = .Err (.Missing e) ∧
      e.val = c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapEntries_length, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_values_quirk_last
/-- `into_positional` (deprecated) of `Params::Empty` or `Params::Positional`: unchanged (the
    statement's names are not checked, unlike `into_values`). -/
recall params.Params.into_positional_not_named (p : params.Params)
    (hp : ∀ m, p ≠ .Named m) (ns : Slice (alloc.vec.Vec U8)) :
    params.Params.into_positional p ns ⦃ r => r = .Ok p ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapRemove, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_positional_not_named
/-- `into_positional` of `Params::Named m` when every name has a value: `Positional` with the
    values in the order of the names. -/
recall params.Params.into_positional_named_ok (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∀ n ∈ ns.val, (Trusted.paramsMapLookup m n.val).isSome) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ v, r = .Ok (.Positional v) ∧
      v.val.map some = ns.val.map (fun n => Trusted.paramsMapLookup m n.val) ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapEntries_remove, Trusted.paramsMapRemove, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_positional_named_ok
/-- `into_positional` of `Params::Named m` when some name has no value: the **first** such name
    is reported. -/
recall params.Params.into_positional_named_missing (m : Trusted.ParamsMap)
    (ns : Slice (alloc.vec.Vec U8))
    (h : ∃ n ∈ ns.val, Trusted.paramsMapLookup m n.val = none) :
    params.Params.into_positional (.Named m) ns ⦃ r => ∃ e, r = .Err e ∧
      (ns.val.find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)).map (·.val) =
        some e.val ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapEntries_remove, Trusted.paramsMapRemove, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.into_positional_named_missing
/-! ### `impl From<&T>`, `From<Vec<T>>`, `From<Vec<(N, V)>>`, `From<()>` for `Params` -/

/-- `From<&T> for Params`: `x.clone().into()`. -/
recall params.Params.Insts.CoreConvertFromSharedAT.from_eq {T : Type}
    (intoInst : core.convert.Into T params.Params) (cloneInst : core.clone.Clone T) (x : T) :
    params.Params.Insts.CoreConvertFromSharedAT.from intoInst cloneInst x =
      (do let t ← cloneInst.clone x; intoInst.into t)

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromSharedAT.from_eq
/-- `From<Vec<T>> for Params`: `Empty` for an empty vector, else `Positional` of the converted
    elements, in order (when each conversion returns). -/
recall params.Params.Insts.CoreConvertFromVec.from_spec {T : Type}
    (inst : core.convert.From value.Value T) (x : alloc.vec.Vec T) (g : T → value.Value)
    (hg : ∀ t ∈ x.val, inst.from t = ok (g t)) :
    params.Params.Insts.CoreConvertFromVec.from inst x ⦃ p =>
      (x.val = [] ∧ p = .Empty) ∨
      (x.val ≠ [] ∧ ∃ w, p = .Positional w ∧ w.val = x.val.map g) ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromVec.from_spec
/-- `From<Vec<(N, V)>> for Params` with distinct names: `Named` of a map whose entries are the
    converted pairs (in an unspecified order). -/
recall params.Params.Insts.CoreConvertFromVecPair.from_spec {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (x : alloc.vec.Vec (N × V)) (gn : N → alloc.vec.Vec U8) (gv : V → value.Value)
    (hn : ∀ e ∈ x.val, nInst.from e.1 = ok (gn e.1))
    (hv : ∀ e ∈ x.val, vInst.from e.2 = ok (gv e.2))
    (hnd : (x.val.map fun e => (gn e.1).val).Nodup) :
    params.Params.Insts.CoreConvertFromVecPair.from nInst vInst x ⦃ p => ∃ m, p = .Named m ∧
      (Trusted.paramsMapEntries m).Perm (x.val.map fun e => (gn e.1, gv e.2)) ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEmpty, Trusted.paramsMapEntries, Trusted.paramsMapEntries_empty, Trusted.paramsMapEntries_insert, Trusted.paramsMapInsert, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromVecPair.from_spec
/-- `From<Vec<(N, V)>> for Params` panics ("Redefinition of named parameter") when two names
    are equal (translated as an assertion failure). (`hv` is stronger than needed: only the
    values before the first repeated name are converted.) -/
recall params.Params.Insts.CoreConvertFromVecPair.from_dup {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (x : alloc.vec.Vec (N × V)) (gn : N → alloc.vec.Vec U8) (gv : V → value.Value)
    (hn : ∀ e ∈ x.val, nInst.from e.1 = ok (gn e.1))
    (hv : ∀ e ∈ x.val, vInst.from e.2 = ok (gv e.2))
    (hd : ¬ (x.val.map fun e => (gn e.1).val).Nodup) :
    params.Params.Insts.CoreConvertFromVecPair.from nInst vInst x = fail .assertionFailure

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEmpty, Trusted.paramsMapEntries, Trusted.paramsMapEntries_empty, Trusted.paramsMapEntries_insert, Trusted.paramsMapEntries_keys_nodup, Trusted.paramsMapInsert, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromVecPair.from_dup
/-- `From<()> for Params`: `Empty`. -/
recall params.Params.Insts.CoreConvertFromTuple.from_eq (u : Unit) :
    params.Params.Insts.CoreConvertFromTuple.from u = ok .Empty

/-- [propext, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTuple.from_eq
/-! ### `into_params_impl!`: `From<(A, ..)> for Params` -/

/-- `From<(A,)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleA.from_spec {A : Type}
    (instA : core.convert.Into A value.Value)
    (a : A) (va : value.Value)
    (ha : instA.into a = ok va) :
    params.Params.Insts.CoreConvertFromTupleA.from instA a ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleA.from_spec
/-- `From<(A, B)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromPair.from_spec {A : Type} {B : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value)
    (a : A) (b : B) (va : value.Value) (vb : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) :
    params.Params.Insts.CoreConvertFromPair.from instA instB (a, b) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromPair.from_spec
/-- `From<(A, B, C)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABC.from_spec {A : Type} {B : Type} {C : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value)
    (a : A) (b : B) (c : C) (va : value.Value) (vb : value.Value) (vc : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) :
    params.Params.Insts.CoreConvertFromTupleABC.from instA instB instC (a, b, c) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABC.from_spec
/-- `From<(A, B, C, D)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCD.from_spec {A : Type} {B : Type} {C : Type} {D : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value)
    (a : A) (b : B) (c : C) (d : D) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) :
    params.Params.Insts.CoreConvertFromTupleABCD.from instA instB instC instD (a, b, c, d) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCD.from_spec
/-- `From<(A, B, C, D, E)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDE.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) :
    params.Params.Insts.CoreConvertFromTupleABCDE.from instA instB instC instD instE (a, b, c, d, e) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDE.from_spec
/-- `From<(A, B, C, D, E, F)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEF.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) :
    params.Params.Insts.CoreConvertFromTupleABCDEF.from instA instB instC instD instE instF (a, b, c, d, e, f) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEF.from_spec
/-- `From<(A, B, C, D, E, F, G)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFG.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) :
    params.Params.Insts.CoreConvertFromTupleABCDEFG.from instA instB instC instD instE instF instG (a, b, c, d, e, f, g) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFG.from_spec
/-- `From<(A, B, C, D, E, F, G, H)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFGH.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGH.from instA instB instC instD instE instF instG instH (a, b, c, d, e, f, g, h) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFGH.from_spec
/-- `From<(A, B, C, D, E, F, G, H, I)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFGHI.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHI.from instA instB instC instD instE instF instG instH instI (a, b, c, d, e, f, g, h, i) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFGHI.from_spec
/-- `From<(A, B, C, D, E, F, G, H, I, J)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFGHIJ.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJ.from instA instB instC instD instE instF instG instH instI instJ (a, b, c, d, e, f, g, h, i, j) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFGHIJ.from_spec
/-- `From<(A, B, C, D, E, F, G, H, I, J, K)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFGHIJK.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type} {K : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value) (instK : core.convert.Into K value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (k : K) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value) (vk : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) (hk : instK.into k = ok vk) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJK.from instA instB instC instD instE instF instG instH instI instJ instK (a, b, c, d, e, f, g, h, i, j, k) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFGHIJK.from_spec
/-- `From<(A, B, C, D, E, F, G, H, I, J, K, L)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
recall params.Params.Insts.CoreConvertFromTupleABCDEFGHIJKL.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type} {K : Type} {L : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value) (instK : core.convert.Into K value.Value) (instL : core.convert.Into L value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (k : K) (l : L) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value) (vk : value.Value) (vl : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) (hk : instK.into k = ok vk) (hl : instL.into l = ok vl) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJKL.from instA instB instC instD instE instF instG instH instI instJ instK instL (a, b, c, d, e, f, g, h, i, j, k, l) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk, vl] ⦄

/-- [propext, Classical.choice, Quot.sound, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms params.Params.Insts.CoreConvertFromTupleABCDEFGHIJKL.from_spec
end mysql_common
