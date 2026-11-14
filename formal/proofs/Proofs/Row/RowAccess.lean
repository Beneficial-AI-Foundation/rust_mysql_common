import Defs
import Proofs.Util.RowAccess

/-! Statements for the accessors of `struct Row` (`as_ref`, `get`, `get_opt`, `take`,
`take_opt`, `unwrap`, `place`; spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open RowAccessUtil

private theorem unwrap_loop_spec (vs : List value.Value) (values : alloc.vec.Vec (Option value.Value))
    (out : alloc.vec.Vec value.Value) (i : Usize)
    (hlen : values.length = vs.length) (hi : i.val ≤ vs.length) (hout : out.val = vs.take i.val)
    (hd : values.val.drop i.val = (vs.map some).drop i.val) :
    row.Row.unwrap_loop values out i ⦃ r => r.val = vs ⦄ := by
  unfold row.Row.unwrap_loop
  apply loop.spec_decr_nat (fun p : _ × _ × Usize => vs.length - p.2.2.val)
    (fun p => p.1.length = vs.length ∧ p.2.2.val ≤ vs.length ∧ p.2.1.val = vs.take p.2.2.val ∧
      p.1.val.drop p.2.2.val = (vs.map some).drop p.2.2.val)
  · clear hlen hi hout hd values out i
    rintro ⟨values, out, i⟩ ⟨hlen, hi, hout, hd⟩
    simp only at hlen hi hout hd
    unfold row.Row.unwrap_loop.body
    simp only [alloc.vec.Vec.index_mut_slice_index]
    step*
    · have hlt : i.val < vs.length := by scalar_tac
      have hvi : values.val[i.val]? = some (some vs[i.val]) := by
        have := congrArg (·[0]?) hd
        simpa [List.getElem?_drop, List.getElem?_eq_getElem hlt] using this
      have ho : o = some vs[i.val] := by
        rw [o_post]; simp [List.getElem?_eq_some_iff] at hvi; exact hvi.2
      simp only [core.option.Option.expect, ho, Result.ofOption, bind_ok]
      step*
      refine ⟨by simp_all, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp_all [List.take_add_one]
      · rw [index_mut_back_post]
        simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val, i2_post]
        rw [List.drop_set_of_lt (by omega)]
        have := congrArg (List.drop 1) hd
        simpa [List.drop_drop, Nat.add_comm] using this
    · have : i.val = vs.length := by scalar_tac
      rw [hout, this, List.take_length]
  · exact ⟨hlen, hi, hout, hd⟩

private theorem unwrap_loop_unfold (values : alloc.vec.Vec (Option value.Value))
    (out : alloc.vec.Vec value.Value) (i : Usize) :
    row.Row.unwrap_loop values out i =
      (do
        let r ← row.Row.unwrap_loop.body values out i
        match r with
        | .cont (a, b, c) => row.Row.unwrap_loop a b c
        | .done x => ok x) := by
  conv_lhs => unfold row.Row.unwrap_loop; rw [loop]
  congr 1
  funext r
  rcases r with ⟨a, b, c⟩ | x <;> rfl

private theorem unwrap_loop_panics (k : Nat) (values : alloc.vec.Vec (Option value.Value))
    (out : alloc.vec.Vec value.Value) (i : Usize)
    (hk : values.length - i.val = k) (hout : out.length = i.val)
    (hn : allCells (values.val.drop i.val) = none) :
    row.Row.unwrap_loop values out i = fail .panic := by
  induction k generalizing values out i with
  | zero =>
    rw [List.drop_of_length_le (by simp at hk; omega)] at hn
    simp [allCells] at hn
  | succ k ih =>
    have hlt : i.val < values.length := by omega
    rw [unwrap_loop_unfold]
    unfold row.Row.unwrap_loop.body
    have hlt' : i < alloc.vec.Vec.len values := by scalar_tac
    simp only [hlt', ↓reduceIte, alloc.vec.Vec.index_mut_slice_index]
    obtain ⟨⟨c, f⟩, hc, hcv, hf⟩ := spec_eq_ok (alloc.vec.Vec.index_mut_usize_spec values i hlt)
    rw [hc, bind_ok]
    rw [List.drop_eq_getElem_cons hlt, ← hcv] at hn
    rcases c with _ | v
    · simp [core.option.Option.take, core.option.Option.expect, Result.ofOption]
    · simp only [allCells, Option.map_eq_none_iff] at hn
      simp only [core.option.Option.take, core.option.Option.expect, Result.ofOption]
      obtain ⟨out1, hp, hp1⟩ := spec_eq_ok (alloc.vec.Vec.push_spec out v (by scalar_tac))
      obtain ⟨i2, hi2, hi2v⟩ := spec_eq_ok (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have hi2v' : i2.val = i.val + 1 := by simpa using hi2v
      simp [hp, hi2]
      apply ih
      · simp [hf]; scalar_tac
      · simp [hp1]; scalar_tac
      · rw [hf]; simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val]
        rw [hi2v', List.drop_set_of_lt (by omega)]; exact hn

/-- `as_ref`: the value in cell `index`, or `None` when there is no such cell or its value was
    taken. Never panics. -/
theorem row.Row.as_ref_eq (self : row.Row) (index : Usize) :
    row.Row.as_ref self index = ok (cellAt self.values.val index.val) := by
  simp only [row.Row.as_ref, core.slice.Slice.get, cellAt, core.option.Option.as_ref,
    core.slice.index.Usize.get, bind_ok, vec_deref_getElem?]
  rcases (self.values.val[index.val]?) with _ | _ | _ <;> rfl

/-- `get`: finds the column with the `ColumnIndex` impl; `None` when there is no such column, or
    its value was taken; otherwise converts a copy of the value with `from_value` (which panics
    when the value does not convert). The row is not changed (`&self`). -/
theorem row.Row.get_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) :
    row.Row.get inst ci self index =
      (ci.idx index self.columns >>= fun o =>
        match cellAtIdx self.values.val o with
        | none => ok none
        | some v => inst.from_value v >>= fun x => ok (some x)) := by
  simp only [row.Row.get, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
  congr 1; funext o
  rcases o with _ | i
  · rfl
  simp only [core.slice.Slice.get, core.slice.index.Usize.get,
    bind_ok, vec_deref_getElem?, cellAtIdx, cellAt, value_clone_eq, value.convert.from_value]
  rcases (self.values.val[i.val]?) with _ | _ | _ <;> rfl

/-- `get_opt`: as `get`, converting with `from_value_opt` (so a value that does not convert
    gives `Some(Err(..))` instead of a panic). -/
theorem row.Row.get_opt_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) :
    row.Row.get_opt inst ci self index =
      (ci.idx index self.columns >>= fun o =>
        match cellAtIdx self.values.val o with
        | none => ok none
        | some v => inst.from_value_opt v >>= fun x => ok (some x)) := by
  simp only [row.Row.get_opt, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
  congr 1; funext o
  rcases o with _ | i
  · rfl
  simp only [core.slice.Slice.get, core.slice.index.Usize.get,
    bind_ok, vec_deref_getElem?, cellAtIdx, cellAt, value_clone_eq, value.convert.from_value_opt]
  rcases (self.values.val[i.val]?) with _ | _ | _ <;> rfl

/-- `take`: `None`, and the row unchanged, when there is no such column or its value was already
    taken; otherwise moves the value out of cell `i` (leaving it empty, the columns unchanged)
    and returns it converted by `from_value` (which panics when the value does not convert). -/
theorem row.Row.take_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) :
    row.Row.take inst ci self index =
      (ci.idx index self.columns >>= fun o =>
        match o with
        | none => ok (none, self)
        | some i =>
          match cellAt self.values.val i.val with
          | none => ok (none, self)
          | some v => inst.from_value v >>= fun x =>
              ok (some x, { self with values := self.values.set i none })) := by
  simp only [row.Row.take, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
  congr 1; funext o
  rcases o with _ | i
  · rfl
  simp only [lift, alloc.vec.Vec.deref_mut, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
    bind_ok, cellAt, value.convert.from_value, core.option.Option.take]
  rcases h : self.values.val[i.val]? with _ | _ | v <;>
    have h' : self.values.slice.val[i.val]? = _ := h
  · simp [h', vec_mk_set_opt_none]
  · simp [h', vec_mk_set_opt_self _ _ h]
  · simp [h', vec_mk_set_opt]; rfl

/-- `take_opt`: as `take`, converting with `from_value_opt`. The cell is left empty even when
    the value does not convert (the value is then only in the `FromValueError`). -/
theorem row.Row.take_opt_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) :
    row.Row.take_opt inst ci self index =
      (ci.idx index self.columns >>= fun o =>
        match o with
        | none => ok (none, self)
        | some i =>
          match cellAt self.values.val i.val with
          | none => ok (none, self)
          | some v => inst.from_value_opt v >>= fun x =>
              ok (some x, { self with values := self.values.set i none })) := by
  simp only [row.Row.take_opt, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
  congr 1; funext o
  rcases o with _ | i
  · rfl
  simp only [lift, alloc.vec.Vec.deref_mut, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
    bind_ok, cellAt, value.convert.from_value_opt, core.option.Option.take]
  rcases h : self.values.val[i.val]? with _ | _ | v <;>
    have h' : self.values.slice.val[i.val]? = _ := h
  · simp [h', vec_mk_set_opt_none]
  · simp [h', vec_mk_set_opt_self _ _ h]
  · simp [h', vec_mk_set_opt]; rfl

/-- `unwrap`: the values, in order, when no value was taken. -/
theorem row.Row.unwrap_spec (self : row.Row) (vs : List value.Value)
    (h : allCells self.values.val = some vs) :
    row.Row.unwrap self ⦃ out => out.val = vs ⦄ := by
  rw [allCells_some_iff] at h
  unfold row.Row.unwrap
  apply unwrap_loop_spec vs
  · simp [h]
  · simp
  · simp [alloc.vec.Vec.with_capacity]
  · simp [h]

/-- `unwrap` panics when some value was taken. -/
theorem row.Row.unwrap_panics (self : row.Row) (h : allCells self.values.val = none) :
    row.Row.unwrap self = fail .panic := by
  unfold row.Row.unwrap
  exact unwrap_loop_panics _ _ _ _ rfl (by simp [alloc.vec.Vec.with_capacity]) (by simpa using h)

/-- `place`: puts `v` in cell `index` (whether or not it was taken), the other cells and the
    columns unchanged. -/
theorem row.Row.place_spec (self : row.Row) (index : Usize) (v : value.Value)
    (h : index.val < self.values.length) :
    row.Row.place self index v ⦃ r =>
      r.values.val = self.values.val.set index.val (some v) ∧ r.columns = self.columns ⦄ := by
  simp only [row.Row.place]
  step*
  simp [index_mut_back_post, alloc.vec.Vec.set]

/-- `place` panics (index out of bounds) when there is no cell `index`. -/
theorem row.Row.place_panics (self : row.Row) (index : Usize) (v : value.Value)
    (h : self.values.length ≤ index.val) :
    row.Row.place self index v = fail .arrayOutOfBounds := by
  simp only [row.Row.place, alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
    alloc.vec.Vec.index_usize]
  simp [alloc.vec.Vec.getElem?_Nat_eq, List.getElem?_eq_none h]

end mysql_common
