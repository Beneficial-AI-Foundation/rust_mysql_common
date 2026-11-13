import Defs
import Proofs.Util.RowAccess
import Proofs.Row.ColumnIndexStr

/-! Statements for `impl Index<&str> for Row` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open RowAccessUtil

/-- The column lookup of `row[name]`, as an equation. -/
private theorem idx_eq (self : row.Row) (index : Str) (o : Option Nat)
    (hi : colIndexByName index.val self.columns.val = o) :
    ∃ j : Option Usize, Shared0Str.Insts.Mysql_commonRowColumnIndex.idx index self.columns = ok j ∧
      j.map (·.val) = o := by
  obtain ⟨j, hj, hjv⟩ := spec_eq_ok (Shared0Str.Insts.Mysql_commonRowColumnIndex.idx_spec index self.columns)
  exact ⟨j, hj, hjv.trans hi⟩

/-- `row[name]`: the value in the cell of the first column named exactly `name` (byte for byte,
    case-sensitive), when it is there. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_ok (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i) (v : value.Value)
    (h : cellAt self.values.val i = some v) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = ok v := by
  obtain ⟨j, hj, hjv⟩ := idx_eq self index _ hi
  rcases j with _ | j
  · simp at hjv
  simp only [Option.map_some, Option.some.injEq] at hjv
  subst hjv
  simp only [row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, hj, alloc.vec.Vec.index_slice_index,
    alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq]
  unfold cellAt at h
  split at h <;> simp_all [core.option.Option.as_ref, core.option.Option.unwrap, Result.ofOption]

/-- `row[name]` panics ("No such column") when no column is named `name`. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_no_column (self : row.Row) (index : Str)
    (hi : colIndexByName index.val self.columns.val = none) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .panic := by
  obtain ⟨j, hj, hjv⟩ := idx_eq self index _ hi
  rcases j with _ | j
  · simp [row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index,
      alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, hj]
  · simp at hjv

/-- `row[name]` panics (`unwrap` on `None`) when the value of the first column named `name` was
    taken. -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_taken (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i)
    (h : self.values.val[i]? = some none) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .panic := by
  obtain ⟨j, hj, hjv⟩ := idx_eq self index _ hi
  rcases j with _ | j
  · simp at hjv
  simp only [Option.map_some, Option.some.injEq] at hjv
  subst hjv
  simp only [row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, hj, alloc.vec.Vec.index_slice_index,
    alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq]
  simp [h, core.option.Option.as_ref, core.option.Option.unwrap, Result.ofOption]

/-- `row[name]` panics (index out of bounds) when the column has no cell. (Impossible for rows
    built by the crate, which have one cell per column.) -/
theorem row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index_oob (self : row.Row) (index : Str) (i : Nat)
    (hi : colIndexByName index.val self.columns.val = some i)
    (h : self.values.length ≤ i) :
    row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index self index = fail .arrayOutOfBounds := by
  obtain ⟨j, hj, hjv⟩ := idx_eq self index _ hi
  rcases j with _ | j
  · simp at hjv
  simp only [Option.map_some, Option.some.injEq] at hjv
  subst hjv
  simp only [row.Row.Insts.CoreOpsIndexIndexSharedAStrValue.index,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok, hj, alloc.vec.Vec.index_slice_index,
    alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq]
  simp [List.getElem?_eq_none h]

end mysql_common
