import Defs

/-! Helper lemmas for the proofs of group ParamsAsSql (`Proofs/Params/*`,
`Proofs/Value/{Escaped,AsSql}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.PASUtil

/-! ## Clones -/

theorem list_clone_ok {α : Type} (l : List α) (cl : α → Result α) (h : ∀ x, cl x = ok x) :
    List.clone cl l = ok ⟨l, rfl⟩ := by
  simp only [List.clone]
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.mapM_with_length, ih, h, pure]

theorem vec_u8_clone_eq (v : alloc.vec.Vec U8) : alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v := by
  simp only [alloc.vec.CloneVec.clone, Slice.clone]
  rw [list_clone_ok _ _ (fun _ => rfl)]
  simp

theorem value_clone_eq (v : value.Value) : value.Value.Insts.CoreCloneClone.clone v = ok v := by
  cases v <;> simp [value.Value.Insts.CoreCloneClone.clone, vec_u8_clone_eq, lift,
    F32.Insts.CoreCloneClone.clone, F64.Insts.CoreCloneClone.clone]

/-! ## Iterators, `From<Vec<_>>` loops -/


theorem next_nil {T : Type} (it : alloc.vec.into_iter.IntoIter T) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

theorem next_cons {T : Type} (it : alloc.vec.into_iter.IntoIter T) (x : T) (l : List T)
    (h : it.val = x :: l) :
    ∃ it', alloc.vec.into_iter.IteratorIntoIter.next it = ok (some x, it') ∧ it'.val = l := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · simp_all
  · rename_i hd tl heq
    rw [h] at heq; cases heq
    exact ⟨_, rfl, by simp⟩

theorem into_iter_eq {T : Type} (v : alloc.vec.Vec T) :
    ∃ it : alloc.vec.into_iter.IntoIter T, alloc.vec.IntoIteratorVec.into_iter v = ok it ∧ it.val = v.val :=
  ⟨v, rfl, rfl⟩

theorem next_spec {T : Type} (it : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IteratorIntoIter.next it ⦃ o it' =>
      o = it.val.head? ∧ it'.val = it.val.tail ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all [WP.uncurry']

theorem from_vec_loop_spec {T : Type} (inst : core.convert.From value.Value T) (g : T → value.Value) :
    ∀ (l : List T) (iter : alloc.vec.into_iter.IntoIter T) (acc : alloc.vec.Vec value.Value),
    iter.val = l → (∀ t ∈ l, inst.from t = ok (g t)) → acc.length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVec.from_loop inst iter acc ⦃ r => r.val = acc.val ++ l.map g ⦄ := by
  intro l
  induction l with
  | nil =>
    intro iter acc hit _ _
    unfold params.Params.Insts.CoreConvertFromVec.from_loop
    rw [loop]
    simp [params.Params.Insts.CoreConvertFromVec.from_loop.body, next_nil iter hit]
  | cons x l ih =>
    intro iter acc hit hg hlen
    unfold params.Params.Insts.CoreConvertFromVec.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVec.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_cons, List.tail_cons] at ho hit' ⊢
    subst ho
    step with (show inst.from x ⦃ v => v = g x ⦄ by rw [hg x (by simp)]; simp) as ⟨v, hv⟩
    step as ⟨acc1, hacc1⟩
    have := ih it' acc1 hit' (fun t ht => hg t (by simp [ht])) (by simp_all; omega)
    unfold params.Params.Insts.CoreConvertFromVec.from_loop at this
    apply WP.spec_mono this
    intro r hr
    simp [hr, hacc1, hv]


theorem lookup_eq_none_iff (m : Trusted.ParamsMap) (k : List U8) :
    Trusted.paramsMapLookup m k = none ↔ ∀ e ∈ Trusted.paramsMapEntries m, e.1.val ≠ k := by
  simp [Trusted.paramsMapLookup, List.find?_eq_none]

theorem from_pair_loop_spec {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (gn : N → alloc.vec.Vec U8) (gv : V → value.Value) :
    ∀ (l : List (N × V)) (iter : alloc.vec.into_iter.IntoIter (N × V)) (m : Trusted.ParamsMap),
    iter.val = l →
    (∀ e ∈ l, nInst.from e.1 = ok (gn e.1)) →
    (∀ e ∈ l, vInst.from e.2 = ok (gv e.2)) →
    (l.map fun e => (gn e.1).val).Nodup →
    (∀ e ∈ l, ∀ e' ∈ Trusted.paramsMapEntries m, e'.1.val ≠ (gn e.1).val) →
    (Trusted.paramsMapEntries m).length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVecPair.from_loop nInst vInst iter m ⦃ r =>
      (Trusted.paramsMapEntries r).Perm
        (l.map (fun e => (gn e.1, gv e.2)) ++ Trusted.paramsMapEntries m) ⦄ := by
  intro l
  induction l with
  | nil =>
    intro iter m hit _ _ _ _ _
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_nil] at ho ⊢
    subst ho
    simp
  | cons x l ih =>
    intro iter m hit hn hv hnd hfresh hlen
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_cons, List.tail_cons] at ho hit' ⊢
    subst ho
    obtain ⟨xn, xv⟩ := x
    have hnone : Trusted.paramsMapLookup m (gn xn).val = none :=
      (lookup_eq_none_iff _ _).mpr (hfresh (xn, xv) (by simp))
    step with (show nInst.from xn ⦃ v => v = gn xn ⦄ by rw [hn (xn, xv) (by simp)]; simp) as ⟨nm, hnm⟩
    subst hnm
    step with (show sql_trusted.params_map_contains_key m (alloc.vec.Vec.deref (gn xn)) ⦃ b => b = false ⦄ by
      simp [sql_trusted.params_map_contains_key, alloc.vec.Vec.deref, hnone]) as ⟨b, hb⟩
    subst hb
    step with massert_spec (¬ (false = true)) (by simp) as ⟨hu⟩
    step with (show vInst.from xv ⦃ v => v = gv xv ⦄ by rw [hv (xn, xv) (by simp)]; simp) as ⟨vv, hvv⟩
    subst hvv
    step with (show sql_trusted.params_map_insert m (gn xn) (gv xv) ⦃ _ m1 =>
        m1 = Trusted.paramsMapInsert m (gn xn) (gv xv) ⦄ by
      simp [sql_trusted.params_map_insert]) as ⟨p, hp⟩
    obtain ⟨o1, m1⟩ := p
    simp only at hp ⊢
    subst hp
    apply WP.spec_bind (Pₘ := fun r => r = .cont (it', Trusted.paramsMapInsert m (gn xn) (gv xv)))
      ((WP.spec_ok _).mpr rfl)
    rintro r rfl
    have hE : (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv))).Perm
        ((gn xn, gv xv) :: Trusted.paramsMapEntries m) :=
      Trusted.paramsMapEntries_insert m (gn xn) (gv xv) hnone (by simp at hlen; omega)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have := ih it' (Trusted.paramsMapInsert m (gn xn) (gv xv)) hit'
      (fun e he => hn e (by simp [he])) (fun e he => hv e (by simp [he])) hnd.2
      (by
        intro e he e' he'
        rcases List.mem_cons.mp (hE.mem_iff.mp he') with h | h
        · subst h; intro heq; exact hnd.1 ⟨e, he, heq.symm⟩
        · exact hfresh e (by simp [he]) e' h)
      (by rw [hE.length_eq]; simp at hlen ⊢; omega)
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop at this
    refine WP.spec_mono this ?_
    intro r hr
    simp only [List.map_cons]
    exact hr.trans ((List.Perm.append_left _ hE).trans List.perm_middle)


theorem from_pair_loop_dup {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (gn : N → alloc.vec.Vec U8) (gv : V → value.Value) :
    ∀ (l : List (N × V)) (iter : alloc.vec.into_iter.IntoIter (N × V)) (m : Trusted.ParamsMap),
    iter.val = l →
    (∀ e ∈ l, nInst.from e.1 = ok (gn e.1)) →
    (∀ e ∈ l, vInst.from e.2 = ok (gv e.2)) →
    ¬ (l.map (fun e => (gn e.1).val) ++ (Trusted.paramsMapEntries m).map (fun e => e.1.val)).Nodup →
    (Trusted.paramsMapEntries m).length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVecPair.from_loop nInst vInst iter m = fail .assertionFailure := by
  intro l
  induction l with
  | nil =>
    intro iter m _ _ _ hnd _
    exact absurd (Trusted.paramsMapEntries_keys_nodup m) (by simpa using hnd)
  | cons x l ih =>
    intro iter m hit hn hv hnd hlen
    obtain ⟨xn, xv⟩ := x
    obtain ⟨it', hnx, hit'⟩ := next_cons iter _ _ hit
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only
    rw [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    simp only [hnx, Std.bind_ok, core.convert.IntoFrom.into]
    simp only [Std.uncurry_apply_pair, hn (xn, xv) (by simp), Std.bind_ok,
      sql_trusted.params_map_contains_key, alloc.vec.Vec.deref, Slice.from_val]
    by_cases hin : (gn xn).val ∈ (Trusted.paramsMapEntries m).map (fun e => e.1.val)
    · have hs : (Trusted.paramsMapLookup m (gn xn).val).isSome = true := by
        cases h : Trusted.paramsMapLookup m (gn xn).val with
        | some _ => rfl
        | none =>
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hin
          exact absurd heq ((lookup_eq_none_iff _ _).mp h e he)
      simp [hs, massert]
    · have hnone : Trusted.paramsMapLookup m (gn xn).val = none := by
        rw [lookup_eq_none_iff]; intro e he heq; exact hin (List.mem_map.mpr ⟨e, he, heq⟩)
      have hE : (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv))).Perm
          ((gn xn, gv xv) :: Trusted.paramsMapEntries m) :=
        Trusted.paramsMapEntries_insert m (gn xn) (gv xv) hnone (by simp at hlen; omega)
      simp only [hnone, Option.isSome_none, massert, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
        Std.bind_ok, hv (xn, xv) (by simp), sql_trusted.params_map_insert, Std.uncurry_apply_pair]
      have := ih it' (Trusted.paramsMapInsert m (gn xn) (gv xv)) hit'
        (fun e he => hn e (by simp [he])) (fun e he => hv e (by simp [he]))
        (by
          intro hnd'
          apply hnd
          have hp : (List.map (fun e => (gn e.1).val) l ++ List.map (fun e => e.1.val)
              (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv)))).Perm
              ((gn xn).val :: (List.map (fun e => (gn e.1).val) l ++
                List.map (fun e => e.1.val) (Trusted.paramsMapEntries m))) :=
            ((List.Perm.append_left _ (hE.map _)).trans List.perm_middle)
          have h2 := hp.nodup_iff.mp hnd'
          simpa using h2)
        (by rw [hE.length_eq]; simp at hlen ⊢; omega)
      unfold params.Params.Insts.CoreConvertFromVecPair.from_loop at this
      simpa using this

end mysql_common.PASUtil
