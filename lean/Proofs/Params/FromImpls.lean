import Defs
import Proofs.Util.ParamsAsSql

/-! Statements for the `From<…> for Params` impls `From<&T>`, `From<Vec<T>>`,
`From<Vec<(N, V)>>` and `From<()>` (spec file: `Specs/Params.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<&T> for Params`: `x.clone().into()`. -/
theorem params.Params.Insts.CoreConvertFromSharedAT.from_eq {T : Type}
    (intoInst : core.convert.Into T params.Params) (cloneInst : core.clone.Clone T) (x : T) :
    params.Params.Insts.CoreConvertFromSharedAT.from intoInst cloneInst x =
      (do let t ← cloneInst.clone x; intoInst.into t) := by
  rfl

/-- `From<Vec<T>> for Params`: `Empty` for an empty vector, else `Positional` of the converted
    elements, in order (when each conversion returns). -/
theorem params.Params.Insts.CoreConvertFromVec.from_spec {T : Type}
    (inst : core.convert.From value.Value T) (x : alloc.vec.Vec T) (g : T → value.Value)
    (hg : ∀ t ∈ x.val, inst.from t = ok (g t)) :
    params.Params.Insts.CoreConvertFromVec.from inst x ⦃ p =>
      (x.val = [] ∧ p = .Empty) ∨
      (x.val ≠ [] ∧ ∃ w, p = .Positional w ∧ w.val = x.val.map g) ⦄ := by
  unfold params.Params.Insts.CoreConvertFromVec.from
  obtain ⟨it, hit, hitv⟩ := PASUtil.into_iter_eq x
  simp only [hit, Std.bind_ok]
  step with PASUtil.from_vec_loop_spec inst g x.val it (alloc.vec.Vec.new value.Value) hitv hg
    (by simp) as ⟨r, hr⟩
  simp only [alloc.vec.Vec.is_empty, Std.bind_ok]
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hr
  by_cases hx : x.val = []
  · simp [hx, hr]
  · simp [hx, hr]

/-- `From<Vec<(N, V)>> for Params` with distinct names: `Named` of a map whose entries are the
    converted pairs (in an unspecified order). -/
theorem params.Params.Insts.CoreConvertFromVecPair.from_spec {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (x : alloc.vec.Vec (N × V)) (gn : N → alloc.vec.Vec U8) (gv : V → value.Value)
    (hn : ∀ e ∈ x.val, nInst.from e.1 = ok (gn e.1))
    (hv : ∀ e ∈ x.val, vInst.from e.2 = ok (gv e.2))
    (hnd : (x.val.map fun e => (gn e.1).val).Nodup) :
    params.Params.Insts.CoreConvertFromVecPair.from nInst vInst x ⦃ p => ∃ m, p = .Named m ∧
      (Trusted.paramsMapEntries m).Perm (x.val.map fun e => (gn e.1, gv e.2)) ⦄ := by
  unfold params.Params.Insts.CoreConvertFromVecPair.from
  obtain ⟨it, hit, hitv⟩ := PASUtil.into_iter_eq x
  simp only [sql_trusted.params_map_new, hit, Std.bind_ok]
  step with PASUtil.from_pair_loop_spec nInst vInst gn gv x.val it Trusted.paramsMapEmpty hitv hn hv hnd
    (by simp [Trusted.paramsMapEntries_empty]) (by simp [Trusted.paramsMapEntries_empty])
    as ⟨r, hr⟩
  exact ⟨r, rfl, by simpa [Trusted.paramsMapEntries_empty] using hr⟩

/-- `From<Vec<(N, V)>> for Params` panics ("Redefinition of named parameter") when two names
    are equal (translated as an assertion failure). (`hv` is stronger than needed: only the
    values before the first repeated name are converted.) -/
theorem params.Params.Insts.CoreConvertFromVecPair.from_dup {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (x : alloc.vec.Vec (N × V)) (gn : N → alloc.vec.Vec U8) (gv : V → value.Value)
    (hn : ∀ e ∈ x.val, nInst.from e.1 = ok (gn e.1))
    (hv : ∀ e ∈ x.val, vInst.from e.2 = ok (gv e.2))
    (hd : ¬ (x.val.map fun e => (gn e.1).val).Nodup) :
    params.Params.Insts.CoreConvertFromVecPair.from nInst vInst x = fail .assertionFailure := by
  unfold params.Params.Insts.CoreConvertFromVecPair.from
  obtain ⟨it, hit, hitv⟩ := PASUtil.into_iter_eq x
  simp only [sql_trusted.params_map_new, hit, Std.bind_ok]
  rw [PASUtil.from_pair_loop_dup nInst vInst gn gv x.val it Trusted.paramsMapEmpty hitv hn hv
    (by simpa [Trusted.paramsMapEntries_empty] using hd)
    (by simp [Trusted.paramsMapEntries_empty])]
  simp

/-- `From<()> for Params`: `Empty`. -/
theorem params.Params.Insts.CoreConvertFromTuple.from_eq (u : Unit) :
    params.Params.Insts.CoreConvertFromTuple.from u = ok .Empty := by
  rfl

end mysql_common
