import Defs
import Proofs.Util.RowAccess

/-! Facts about the row access and row conversion definitions (spec file:
`Specs/DefsRowConvert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common

namespace Defs

private theorem errStop_converted (ws : List value.Value) (os : List (Option CellOutcome)) :
    errStop (ws.map (fun w => some (CellOutcome.converted w)) ++ os) =
      (errStop os).map (fun p => (ws.map some ++ p.1, p.2)) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.cons_append, errStop, ih, Option.map_map]
    rfl

private theorem errStop_passed (n : Nat) (os : List (Option CellOutcome)) :
    errStop (List.replicate n (some CellOutcome.passed) ++ os) =
      (errStop os).map (fun p => (List.replicate n none ++ p.1, p.2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, errStop, ih, Option.map_map]
    rfl

private theorem allCells_map_some {α : Type} (ws : List α) : allCells (ws.map some) = some ws :=
  (mysql_common.RowAccessUtil.allCells_some_iff _ _).mpr rfl

/-- `colIndexByName` is the first match: `i` is found exactly when column `i` has the name and no
    column before it does. -/
theorem colIndexByName_eq_some_iff (nm : List U8) (cols : List packets.Column) (i : Nat) :
    colIndexByName nm cols = some i ↔
      (cols[i]?.map colName = some nm ∧ ∀ j < i, cols[j]?.map colName ≠ some nm) := by
  unfold colIndexByName
  rw [List.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hi, hp, hj⟩
    refine ⟨by simp [List.getElem?_eq_getElem hi]; simpa using hp, ?_⟩
    intro j hji
    have hj' : j < cols.length := by omega
    simp [List.getElem?_eq_getElem hj']
    simpa using hj j hji
  · rintro ⟨hp, hj⟩
    have hi : i < cols.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hp; simp at hp
    refine ⟨hi, ?_, ?_⟩
    · simp [List.getElem?_eq_getElem hi] at hp; simpa using hp
    · intro j hji
      have := hj j hji
      simp [List.getElem?_eq_getElem (show j < cols.length by omega)] at this
      simpa using this

/-- `colIndexByName` finds nothing exactly when no column has the name. -/
theorem colIndexByName_eq_none_iff (nm : List U8) (cols : List packets.Column) :
    colIndexByName nm cols = none ↔ ∀ c ∈ cols, colName c ≠ nm := by
  unfold colIndexByName
  rw [List.findIdx?_eq_none_iff]
  simp

/-- No error row when every cell converts. -/
theorem fromRowErrCells_all_converted (cells : List (Option value.Value)) (ws : List value.Value) :
    fromRowErrCells cells (ws.map fun w => some (.converted w)) = none := by
  unfold fromRowErrCells
  have := errStop_converted ws []
  simp only [List.append_nil] at this
  rw [this]; simp [errStop]

/-- A rejected cell: the cells before it come back as the rollback values, it comes back as the
    rejected value, the rest unchanged. -/
theorem fromRowErrCells_rejected (vs ws : List value.Value) (v e : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected e) :: os) =
      some (ws.map some ++ some e :: rest) := by
  unfold fromRowErrCells
  rw [errStop_converted]
  simp [errStop, allCells_map_some, h, List.drop_append]

/-- After a rejected cell whose error carries the original value, the row comes back unchanged
    exactly when every earlier rollback gives back the original value. -/
theorem fromRowErrCells_rejected_restores_iff (vs ws : List value.Value) (v : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected v) :: os) =
      some (vs.map some ++ some v :: rest) ↔ ws = vs := by
  rw [fromRowErrCells_rejected vs ws v v rest os h]
  simp only [Option.some.injEq]
  constructor
  · intro he
    have := List.append_inj_left he (by simp [h])
    exact List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h) this
  · rintro rfl; rfl

/-- A taken cell: it and every cell before it come back empty, the rest unchanged. -/
theorem fromRowErrCells_taken (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) =
      some (List.replicate (vs.length + 1) none ++ rest) := by
  unfold fromRowErrCells
  rw [errStop_converted]
  simp [errStop, h, List.drop_append]

/-- The data loss: after a taken cell that is not the first, the row does not come back
    unchanged. -/
theorem fromRowErrCells_taken_ne (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) (hne : vs ≠ []) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) ≠
      some (vs.map some ++ none :: rest) := by
  rw [fromRowErrCells_taken vs ws rest os h]
  obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [List.replicate_succ]

/-- `allCells` is every value exactly when no cell is empty. -/
theorem allCells_eq_some_iff {α : Type} (cells : List (Option α)) (vs : List α) :
    allCells cells = some vs ↔ cells = vs.map some := by
  exact mysql_common.RowAccessUtil.allCells_some_iff cells vs

/-- A taken cell after cells that only `passed` (no rollback known): the same row as after
    `converted` cells, since no rollback happens. -/
theorem fromRowErrCells_taken_passed (vs : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (List.replicate vs.length (some .passed) ++ some .taken :: os) =
      some (List.replicate (vs.length + 1) none ++ rest) := by
  unfold fromRowErrCells
  rw [errStop_passed]
  simp [errStop, List.drop_append]

/-- A rejected cell after a cell that only `passed`: nothing is described (the rollback of the
    earlier cell is needed). -/
theorem fromRowErrCells_rejected_passed (c : Option value.Value) (cells : List (Option value.Value))
    (e : value.Value) (os : List (Option CellOutcome)) :
    fromRowErrCells (c :: cells) (some .passed :: some (.rejected e) :: os) = none := by
  simp [fromRowErrCells, errStop, allCells]

/-- `DefaultFromValue` for `i8` (by `⟨rfl, rfl⟩`, as for every impl of the crate). -/
theorem defaultFromValue_i8 :
    DefaultFromValue I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 := by
  exact ⟨rfl, rfl⟩

/-- `DefaultFromValue` for `i64`. -/
theorem defaultFromValue_i64 :
    DefaultFromValue I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 := by
  exact ⟨rfl, rfl⟩

/-- `DefaultFromValue` for `String`. -/
theorem defaultFromValue_string :
    DefaultFromValue alloc.string.String.Insts.Mysql_commonValueConvertFromValueString := by
  exact ⟨rfl, rfl⟩

/-- `DefaultFromValue` for `Value` itself. -/
theorem defaultFromValue_value :
    DefaultFromValue value.Value.Insts.Mysql_commonValueConvertFromValueValueIr := by
  exact ⟨rfl, rfl⟩

end Defs
