import Defs
set_option autoImplicit false
open Aeneas Aeneas.Std Result mysql_common Defs
/-! Helper lemmas for the proofs of the tuple `FromRow` impls (`Proofs/Row/Convert/Tuple*.lean`). -/

namespace mysql_common.RowTuples

private theorem set_opt_some {α : Type} (l : List α) (i : Nat) (x : α) :
    l.set_opt i (some x) = l.set i x := by
  induction l generalizing i with
  | nil => simp [List.set_opt]
  | cons hd tl ih => cases i <;> simp_all [List.set_opt]

private theorem set_opt_none {α : Type} (l : List α) (i : Nat) :
    l.set_opt i none = l := by
  induction l generalizing i with
  | nil => simp [List.set_opt]
  | cons hd tl ih => cases i <;> simp_all [List.set_opt]

/-- `Row::take::<Value, usize>`: the cell's content and the row with that cell emptied, when the
    index is below the column count; nothing (row unchanged) otherwise. -/
theorem take_eq (r : row.Row) (k : Usize) :
    row.Row.take value.Value.Insts.Mysql_commonValueConvertFromValueValueIr
      Usize.Insts.Mysql_commonRowColumnIndex r k =
    ok (if k.val < r.columns.length then
          ((r.values.val[k.val]?).join, { r with values := r.values.set k none })
        else (none, r)) := by
  have hfv : ∀ v, value.convert.from_value value.Value.Insts.Mysql_commonValueConvertFromValueValueIr v = ok v := by
    intro v
    simp [value.convert.from_value,
      value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from,
      core.convert.IntoFrom.into, value.Value.Insts.CoreConvertFromValueIr.from]
  by_cases hk : k.val < r.columns.length
  · have hk' : ¬ (r.columns.val.length ≤ k.val) := by scalar_tac
    rcases hc : r.values.val[k.val]? with _ | _ | v <;>
      simp [row.Row.take, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
        Usize.Insts.Mysql_commonRowColumnIndex.idx, hk, hk', core.slice.Slice.get_mut,
        alloc.vec.Vec.deref_mut, hfv, core.option.Option.take, lift] <;>
      simp only [show r.values.slice.val = r.values.val from rfl, hc] <;>
      congr 3 <;> apply alloc.vec.Vec.ext <;>
      simp [alloc.vec.Vec.val, Slice.set_opt, set_opt_some, set_opt_none]
    · show r.values.val = (r.values.set k none).val
      rw [alloc.vec.Vec.set_val_eq, List.set_eq_of_length_le (List.getElem?_eq_none_iff.mp hc)]
    all_goals
      show _ = (r.values.set k none).val
      rw [alloc.vec.Vec.set_val_eq]; rfl
  · have hk' : (r.columns.val.length ≤ k.val) := by scalar_tac
    simp [row.Row.take, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
      Usize.Insts.Mysql_commonRowColumnIndex.idx, hk, hk']

theorem take_eq_lt (r : row.Row) (k : Usize) (hk : k.val < r.columns.val.length) :
    row.Row.take value.Value.Insts.Mysql_commonValueConvertFromValueValueIr
      Usize.Insts.Mysql_commonRowColumnIndex r k =
    ok ((r.values.val[k.val]?).join, { r with values := r.values.set k none }) := by
  rw [take_eq]; simp [hk]

theorem take_eq_ge (r : row.Row) (k : Usize) (hk : ¬ k.val < r.columns.val.length) :
    row.Row.take value.Value.Insts.Mysql_commonValueConvertFromValueValueIr
      Usize.Insts.Mysql_commonRowColumnIndex r k = ok (none, r) := by
  rw [take_eq]; simp [hk]

/-- `Row::place`: puts the value in the cell (in bounds). -/
theorem place_eq (r : row.Row) (k : Usize) (v : value.Value) :
    row.Row.place r k v =
    if k.val < r.values.length then ok { r with values := r.values.set k (some v) }
    else fail .arrayOutOfBounds := by
  by_cases hk : k.val < r.values.length
  · have : r.values.slice.val[k.val]? = some (r.values.val[k.val]) := by
      show r.values.val[k.val]? = _
      simp [hk]
    simp [row.Row.place, alloc.vec.Vec.index_mut, Slice.index_mut_usize, Slice.index_usize, this, hk, pure_tc_eq]
    apply alloc.vec.Vec.ext
    show _ = (r.values.set k (some v)).val
    rw [alloc.vec.Vec.set_val_eq]
    simp [alloc.vec.Vec.val, Slice.set_val_eq]
  · have : r.values.slice.val[k.val]? = none := by
      show r.values.val[k.val]? = _
      simp; scalar_tac
    simp [row.Row.place, alloc.vec.Vec.index_mut, Slice.index_mut_usize, Slice.index_usize, this, hk, - bind_pure_comp]

theorem place_eq_lt (r : row.Row) (k : Usize) (v : value.Value) (hk : k.val < r.values.val.length) :
    row.Row.place r k v = ok { r with values := r.values.set k (some v) } := by
  rw [place_eq]; simp [hk]

/-- `Vec::len` compared with a constant (as `simp` leaves it). -/
@[simp] theorem ofNatCore_eq_iff (n : Nat) (h : n < 2 ^ UScalarTy.Usize.numBits) (k : Usize) :
    Usize.ofNatCore n h = k ↔ n = k.val := by
  constructor
  · rintro rfl; simp [Usize.ofNatCore]
  · intro hk; apply UScalar.eq_of_val_eq; simp [Usize.ofNatCore, hk]

/-! ## Binds -/

theorem bind_eq_ok_iff {α β : Type} (m : Result α) (k : α → Result β) (w : β) :
    (m >>= k) = ok w ↔ ∃ a, m = ok a ∧ k a = ok w := by
  constructor
  · intro h; cases m <;> simp_all
  · rintro ⟨a, rfl, h⟩; simpa using h

theorem bind_eq_ok_iff' {α β : Type} (m : Result α) (k : α → Result β) (w : β) :
    Std.bind m k = ok w ↔ ∃ a, m = ok a ∧ k a = ok w := bind_eq_ok_iff m k w

/-- A bind on a `Result` of a `core.result.Result`, matched on: it returns exactly when the
    first computation returns and the branch taken returns. -/
theorem bind_match_eq_ok_iff {α ε β : Type} (m : Result (core.result.Result α ε))
    (f : α → Result β) (g : ε → Result β) (w : β) :
    (m >>= fun r => match r with | .Ok a => f a | .Err e => g e) = ok w ↔
      (∃ a, m = ok (.Ok a) ∧ f a = ok w) ∨ (∃ e, m = ok (.Err e) ∧ g e = ok w) := by
  rw [bind_eq_ok_iff]
  constructor
  · rintro ⟨a | e, h1, h2⟩
    · exact Or.inl ⟨a, h1, h2⟩
    · exact Or.inr ⟨e, h1, h2⟩
  · rintro (⟨a, h1, h2⟩ | ⟨e, h1, h2⟩)
    · exact ⟨_, h1, h2⟩
    · exact ⟨_, h1, h2⟩

/-! ## Cell outcomes -/

/-- A converting outcome: `converted w` when the rollback `w` is known, `passed` otherwise. -/
def ofWo : Option value.Value → CellOutcome
  | some w => .converted w
  | none => .passed

@[simp] theorem errStop_ofWo (wo : Option value.Value) (os : List (Option CellOutcome)) :
    errStop (some (ofWo wo) :: os) = (errStop os).map fun p => (wo :: p.1, p.2) := by
  cases wo <;> simp [ofWo, errStop]

@[simp] theorem errStop_none (os : List (Option CellOutcome)) :
    errStop (none :: os) = none := rfl

@[simp] theorem errStop_taken (os : List (Option CellOutcome)) :
    errStop (some .taken :: os) = some ([], none) := rfl

@[simp] theorem errStop_rejected (e : value.Value) (os : List (Option CellOutcome)) :
    errStop (some (.rejected e) :: os) = some ([], some e) := rfl

@[simp] theorem errStop_nil : errStop [] = none := rfl

@[simp] theorem allCells_nil' : allCells ([] : List (Option value.Value)) = some [] := rfl

@[simp] theorem allCells_cons' (a : Option value.Value) (l : List (Option value.Value)) :
    allCells (a :: l) = a.bind fun v => (allCells l).map (v :: ·) := by
  cases a <;> rfl

/-- The four shapes of a described cell outcome. -/
theorem ofOpt_cases {T I : Type} {inst : value.convert.FromValue T I}
    {back : I → Result value.Value} {c : Option value.Value} {o : Option CellOutcome}
    (h : CellOutcome.OfOpt inst back c o) :
    o = none ∨ (o = some .taken ∧ c = none) ∨
    (∃ v e, o = some (.rejected e) ∧ c = some v ∧ inst.get_intermediate v = ok (.Err e)) ∨
    (∃ v ir wo, o = some (ofWo wo) ∧ c = some v ∧ inst.get_intermediate v = ok (.Ok ir) ∧
      ∀ w, wo = some w → back ir = ok w) := by
  rcases o with _ | (_ | e | w | _)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · obtain ⟨v, hc, hg⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨v, e, rfl, hc, hg⟩))
  · obtain ⟨v, ir, hc, hg, hb⟩ := h
    refine Or.inr (Or.inr (Or.inr ⟨v, ir, some w, rfl, hc, hg, ?_⟩))
    intro w' hw'; cases hw'; exact hb
  · obtain ⟨v, ir, hc, hg⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨v, ir, none, rfl, hc, hg, by simp⟩))

/-- With the default `FromValue` methods, `from_value_opt` succeeds exactly when the intermediate
    is `Ok` and turns into the value. -/
theorem from_value_opt_ok_iff {T I : Type} {inst : value.convert.FromValue T I}
    (hd : DefaultFromValue inst) (v : value.Value) (x : T) :
    inst.from_value_opt v = ok (.Ok x) ↔
      ∃ ir, inst.get_intermediate v = ok (.Ok ir) ∧ inst.coreconvertIntoInst.into ir = ok x := by
  rw [hd.1, hd.2]
  simp only [value.convert.FromValue.from_value_opt.default,
    value.convert.FromValue.get_intermediate.default]
  rw [bind_eq_ok_iff']
  constructor
  · rintro ⟨a | e, h1, h2⟩
    · rw [bind_eq_ok_iff'] at h2
      obtain ⟨t, ht, h2⟩ := h2
      simp at h2; subst h2
      exact ⟨a, h1, ht⟩
    · simp at h2
  · rintro ⟨ir, h1, h2⟩
    exact ⟨_, h1, by simp [h2]⟩

end mysql_common.RowTuples

/-! ## Tactics

The tuple impls are uniform per arity, and so are their proofs. These macros are unhygienic: they
use the names of the statements (`r`, `h`, `he`, `hlt`, `hlv`). -/

set_option hygiene false in
/-- `from_row_opt_ok_iff`, forward direction, cell `k` (value `c`, `FromValue` impl `inst`):
    the branches where the conversion fails are closed (they return `Err`); in the one where the
    cell holds a value with an `Ok` intermediate, `h` is left on the rest of the conversion. -/
macro "row_fwd_cell " k:num c:ident inst:ident : tactic => `(tactic| (
  by_cases hk : $k < r.columns.val.length
  swap; · simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt] at h
  rcases $c:ident with _ | v
  · simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt] at h
  cases hg : value.convert.FromValue.get_intermediate $inst v
  case vis => simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt] at h
  case div => simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt] at h
  rename_i a; rcases a with ir | e
  swap; · simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt, mysql_common.RowTuples.bind_eq_ok_iff, mysql_common.RowTuples.bind_eq_ok_iff'] at h
  simp [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt] at h))

set_option hygiene false in
/-- `from_row_opt_ok_iff`, forward direction, after every cell: the conversions of the
    intermediates. -/
macro "row_fwd_finish" : tactic => `(tactic| (
  refine ⟨by scalar_tac, ?_⟩
  simp [mysql_common.RowTuples.bind_eq_ok_iff, mysql_common.RowTuples.bind_eq_ok_iff'] at h
  simp_all))

set_option hygiene false in
/-- `from_row_opt_err`, at the first failing cell (taken or rejected): the row that comes back. -/
macro "row_err_leaf" : tactic => `(tactic| (
  simp (maxSteps := 2000000) [Option.bind_eq_some_iff] at he
  repeat obtain ⟨_, he⟩ := he
  subst_vars
  simp (maxSteps := 2000000) [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt]))

set_option hygiene false in
/-- `from_row_opt_err`, cell with outcome hypothesis `hc`: closes the cases where the cell is the
    first failing one (or nothing is described); in the one where it converts, the goal is left
    on the rest of the conversion. -/
macro "row_err_cell " hc:ident : tactic => `(tactic| (
  rcases mysql_common.RowTuples.ofOpt_cases $hc with
    rfl | ⟨rfl, rfl⟩ | ⟨_, _, rfl, rfl, _⟩ | ⟨_, _, _, rfl, rfl, _, _⟩
  · simp (maxSteps := 2000000) at he
  · row_err_leaf
  · row_err_leaf
  simp (maxSteps := 2000000) [*, row.Row.len, mysql_common.RowTuples.take_eq_lt, mysql_common.RowTuples.take_eq_ge, mysql_common.RowTuples.place_eq_lt]))
