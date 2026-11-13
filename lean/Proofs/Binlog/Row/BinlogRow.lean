import Defs
import Proofs.Util.RowAccess

/-! Statements for `struct BinlogRow and its impls` (spec file: `Specs/Binlog/Row.lean`). Helper lemmas: `Proofs/Util/RowAccess.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open RowAccessUtil

/-- `unwrap_values` on cells that all hold a value: those values, in order. -/
private theorem unwrap_values_some (vs : List binlog.value.BinlogValue) :
    ∀ (values : alloc.vec.Vec (Option binlog.value.BinlogValue)), values.val = vs.map some →
      ∃ out, binlog.row.unwrap_values values = ok out ∧ out.val = vs := by
  induction vs using List.reverseRecOn with
  | nil =>
    intro values h
    rw [binlog.row.unwrap_values]
    simp [alloc.vec.Vec.pop, h]
  | append_singleton xs x ih =>
    intro values h
    have hlen := values.property
    rw [binlog.row.unwrap_values]
    simp only [alloc.vec.Vec.pop, h]
    simp
    obtain ⟨out, hout, hval⟩ := ih (alloc.vec.Vec.from (List.map some xs)
      (by simp [h] at hlen ⊢; omega)) (by simp [alloc.vec.Vec.from_val])
    rw [hout]
    simp only [bind_ok]
    have hl : out.val.length < Usize.max := by
      simp [h] at hlen; simp [hval]; omega
    obtain ⟨v1, hv1, hv1v⟩ := spec_eq_ok (alloc.vec.Vec.push_spec out x hl)
    exact ⟨v1, hv1, by rw [hv1v, hval]⟩

/-- `unwrap_values` panics when some cell is empty. -/
private theorem unwrap_values_none (cells : List (Option binlog.value.BinlogValue)) :
    ∀ (values : alloc.vec.Vec (Option binlog.value.BinlogValue)), values.val = cells →
      allCells cells = none → binlog.row.unwrap_values values = fail .panic := by
  induction cells using List.reverseRecOn with
  | nil => intro values _ h; simp [allCells] at h
  | append_singleton cs c ih =>
    intro values h hnone
    have hlen := values.property
    rw [binlog.row.unwrap_values]
    simp only [alloc.vec.Vec.pop, h]
    simp
    rcases hcs : allCells cs with _ | vs
    · rw [ih _ (by simp [alloc.vec.Vec.from_val]) hcs]; simp
    · obtain ⟨out, hout, _⟩ := unwrap_values_some vs
        (alloc.vec.Vec.from cs (by simp [h] at hlen; omega))
        (by rw [allCells_some_iff] at hcs; simp [alloc.vec.Vec.from_val, hcs])
      rw [hout]
      rcases c with _ | x
      · simp
      · exfalso
        rw [allCells_some_iff] at hcs
        have : allCells (cs ++ [some x]) = some (vs ++ [x]) := by
          rw [allCells_some_iff]; simp [hcs]
        rw [this] at hnone; cases hnone

/-- `new`: the row of the given cells and columns (no length check, unlike `Row`'s `new_row`). -/
theorem binlog.row.BinlogRow.new_eq (values : alloc.vec.Vec (Option binlog.value.BinlogValue))
    (columns : alloc.sync.Arc (Slice packets.Column)) :
    binlog.row.BinlogRow.new values columns = ok { values, columns } := by
  rfl

/-- `len`: the number of cells. -/
theorem binlog.row.BinlogRow.len_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.len self ⦃ n => n.val = self.values.length ⦄ := by
  simp [binlog.row.BinlogRow.len]

/-- `is_empty`: no cells. -/
theorem binlog.row.BinlogRow.is_empty_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.is_empty self ⦃ b => (b ↔ self.values.val = []) ⦄ := by
  simp [binlog.row.BinlogRow.is_empty, alloc.vec.Vec.is_empty]

/-- `columns_ref`: the columns. -/
theorem binlog.row.BinlogRow.columns_ref_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.columns_ref self = ok self.columns := by
  rfl

/-- `columns`: (another `Arc` to) the columns. -/
theorem binlog.row.BinlogRow.impl.columns_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.impl.columns self = ok self.columns := by
  rfl

/-- `as_ref`: the value in cell `index`, or `None` when there is no such cell or its value was taken. Never panics. -/
theorem binlog.row.BinlogRow.as_ref_eq (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.as_ref self index = ok (binlogCellAt self.values.val index.val) := by
  simp only [binlog.row.BinlogRow.as_ref, core.slice.Slice.get, binlogCellAt,
    core.option.Option.as_ref, core.slice.index.Usize.get, bind_ok, vec_deref_getElem?]
  rcases (self.values.val[index.val]?) with _ | _ | _ <;> rfl

/-- `take`: the value in cell `index` (as `as_ref`), moved out: the cell is left empty (a missing cell: nothing changes), the columns unchanged. Never panics. -/
theorem binlog.row.BinlogRow.take_spec (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.take self index ⦃ o r =>
      o = binlogCellAt self.values.val index.val ∧
        r.values.val = self.values.val.set index.val none ∧ r.columns = self.columns ⦄ := by
  simp only [binlog.row.BinlogRow.take, lift, alloc.vec.Vec.deref_mut, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, bind_ok, binlogCellAt, core.option.Option.take]
  rcases h : self.values.val[index.val]? with _ | _ | v <;>
    have h' : self.values.slice.val[index.val]? = _ := h
  · have hle : self.values.val.length ≤ index.val := List.getElem?_eq_none_iff.mp h
    simp [h', vec_mk_set_opt_none, List.set_eq_of_length_le hle]
  · simp [h', vec_mk_set_opt_self _ _ h]
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
    rw [← hget, List.set_getElem_self]
  · simp [h', vec_mk_set_opt, alloc.vec.Vec.set]

/-- `unwrap`: the values, in order, when no value was taken. -/
theorem binlog.row.BinlogRow.unwrap_spec (self : binlog.row.BinlogRow) (vs : List binlog.value.BinlogValue)
    (h : allCells self.values.val = some vs) :
    binlog.row.BinlogRow.unwrap self ⦃ out => out.val = vs ⦄ := by
  rw [allCells_some_iff] at h
  obtain ⟨out, hout, hval⟩ := unwrap_values_some vs self.values h
  simp [binlog.row.BinlogRow.unwrap, hout, hval]

/-- `unwrap` panics when some value was taken (documented). -/
theorem binlog.row.BinlogRow.unwrap_panics (self : binlog.row.BinlogRow) (h : allCells self.values.val = none) :
    binlog.row.BinlogRow.unwrap self = fail .panic := by
  exact unwrap_values_none _ self.values rfl h

/-- `place`: puts `value` in cell `index` (whether or not it was taken), the other cells and the columns unchanged. -/
theorem binlog.row.BinlogRow.place_spec (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : index.val < self.values.length) :
    binlog.row.BinlogRow.place self index value ⦃ r =>
      r.values.val = self.values.val.set index.val (some value) ∧ r.columns = self.columns ⦄ := by
  simp only [binlog.row.BinlogRow.place]
  step*
  simp [index_mut_back_post, alloc.vec.Vec.set]

/-- `place` panics (index out of bounds) when there is no cell `index`. -/
theorem binlog.row.BinlogRow.place_panics (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : self.values.length ≤ index.val) :
    binlog.row.BinlogRow.place self index value = fail .arrayOutOfBounds := by
  simp only [binlog.row.BinlogRow.place, alloc.vec.Vec.index_mut_slice_index,
    alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize]
  simp [alloc.vec.Vec.getElem?_Nat_eq, List.getElem?_eq_none h]

end mysql_common
