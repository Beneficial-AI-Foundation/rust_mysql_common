import Defs

/-! Facts about the row access and row conversion definitions (spec file:
`Specs/DefsRowConvert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common

namespace Defs

/-- `colIndexByName` is the first match: `i` is found exactly when column `i` has the name and no
    column before it does. -/
theorem colIndexByName_eq_some_iff (nm : List U8) (cols : List packets.Column) (i : Nat) :
    colIndexByName nm cols = some i ↔
      (cols[i]?.map colName = some nm ∧ ∀ j < i, cols[j]?.map colName ≠ some nm) := by
  sorry

/-- `colIndexByName` finds nothing exactly when no column has the name. -/
theorem colIndexByName_eq_none_iff (nm : List U8) (cols : List packets.Column) :
    colIndexByName nm cols = none ↔ ∀ c ∈ cols, colName c ≠ nm := by
  sorry

/-- No error row when every cell converts. -/
theorem fromRowErrCells_all_converted (cells : List (Option value.Value)) (ws : List value.Value) :
    fromRowErrCells cells (ws.map fun w => some (.converted w)) = none := by
  sorry

/-- A rejected cell: the cells before it come back as the rollback values, it comes back as the
    rejected value, the rest unchanged. -/
theorem fromRowErrCells_rejected (vs ws : List value.Value) (v e : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected e) :: os) =
      some (ws.map some ++ some e :: rest) := by
  sorry

/-- After a rejected cell whose error carries the original value, the row comes back unchanged
    exactly when every earlier rollback gives back the original value. -/
theorem fromRowErrCells_rejected_restores_iff (vs ws : List value.Value) (v : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected v) :: os) =
      some (vs.map some ++ some v :: rest) ↔ ws = vs := by
  sorry

/-- A taken cell: it and every cell before it come back empty, the rest unchanged. -/
theorem fromRowErrCells_taken (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) =
      some (List.replicate (vs.length + 1) none ++ rest) := by
  sorry

/-- The data loss: after a taken cell that is not the first, the row does not come back
    unchanged. -/
theorem fromRowErrCells_taken_ne (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) (hne : vs ≠ []) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) ≠
      some (vs.map some ++ none :: rest) := by
  sorry

/-- `allCells` is every value exactly when no cell is empty. -/
theorem allCells_eq_some_iff {α : Type} (cells : List (Option α)) (vs : List α) :
    allCells cells = some vs ↔ cells = vs.map some := by
  sorry

/-- A taken cell after cells that only `passed` (no rollback known): the same row as after
    `converted` cells, since no rollback happens. -/
theorem fromRowErrCells_taken_passed (vs : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (List.replicate vs.length (some .passed) ++ some .taken :: os) =
      some (List.replicate (vs.length + 1) none ++ rest) := by
  sorry

/-- A rejected cell after a cell that only `passed`: nothing is described (the rollback of the
    earlier cell is needed). -/
theorem fromRowErrCells_rejected_passed (c : Option value.Value) (cells : List (Option value.Value))
    (e : value.Value) (os : List (Option CellOutcome)) :
    fromRowErrCells (c :: cells) (some .passed :: some (.rejected e) :: os) = none := by
  sorry

/-- `DefaultFromValue` for `i8` (by `⟨rfl, rfl⟩`, as for every impl of the crate). -/
theorem defaultFromValue_i8 :
    DefaultFromValue I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 := by
  sorry

/-- `DefaultFromValue` for `i64`. -/
theorem defaultFromValue_i64 :
    DefaultFromValue I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 := by
  sorry

/-- `DefaultFromValue` for `String`. -/
theorem defaultFromValue_string :
    DefaultFromValue alloc.string.String.Insts.Mysql_commonValueConvertFromValueString := by
  sorry

/-- `DefaultFromValue` for `Value` itself. -/
theorem defaultFromValue_value :
    DefaultFromValue value.Value.Insts.Mysql_commonValueConvertFromValueValueIr := by
  sorry

end Defs
