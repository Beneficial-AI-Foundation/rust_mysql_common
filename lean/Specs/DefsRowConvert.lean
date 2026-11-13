import Proofs.Defs.LemmasRowConvert

/-!
# Facts about the row access and row conversion definitions (`lean/Defs/RowConvert.lean`)

Pure-Lean properties of the definitions used by `Specs/Row.lean` (the accessors) and
`Specs/Row/Convert*.lean`: `colIndexByName` is the first match by name; `fromRowErrCells` in the
three cases (no failure, a rejected cell, a taken cell), including the data loss on a taken cell
and when a rejected conversion gives the original row back; `allCells`; and that the crate's
`FromValue` impls satisfy `DefaultFromValue` (two examples). Proofs:
`Proofs/Defs/LemmasRowConvert.lean`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common

namespace Defs

/-- `colIndexByName` is the first match: `i` is found exactly when column `i` has the name and no
    column before it does. -/
recall colIndexByName_eq_some_iff (nm : List U8) (cols : List packets.Column) (i : Nat) :
    colIndexByName nm cols = some i ↔
      (cols[i]?.map colName = some nm ∧ ∀ j < i, cols[j]?.map colName ≠ some nm)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.colIndexByName_eq_some_iff`
/-- `colIndexByName` finds nothing exactly when no column has the name. -/
recall colIndexByName_eq_none_iff (nm : List U8) (cols : List packets.Column) :
    colIndexByName nm cols = none ↔ ∀ c ∈ cols, colName c ≠ nm

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.colIndexByName_eq_none_iff`
/-- No error row when every cell converts. -/
recall fromRowErrCells_all_converted (cells : List (Option value.Value)) (ws : List value.Value) :
    fromRowErrCells cells (ws.map fun w => some (.converted w)) = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fromRowErrCells_all_converted`
/-- A rejected cell: the cells before it come back as the rollback values, it comes back as the
    rejected value, the rest unchanged. -/
recall fromRowErrCells_rejected (vs ws : List value.Value) (v e : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected e) :: os) =
      some (ws.map some ++ some e :: rest)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fromRowErrCells_rejected`
/-- After a rejected cell whose error carries the original value, the row comes back unchanged
    exactly when every earlier rollback gives back the original value. -/
recall fromRowErrCells_rejected_restores_iff (vs ws : List value.Value) (v : value.Value)
    (rest : List (Option value.Value)) (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ some v :: rest)
        (ws.map (fun w => some (.converted w)) ++ some (.rejected v) :: os) =
      some (vs.map some ++ some v :: rest) ↔ ws = vs

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fromRowErrCells_rejected_restores_iff`
/-- A taken cell: it and every cell before it come back empty, the rest unchanged. -/
recall fromRowErrCells_taken (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) =
      some (List.replicate (vs.length + 1) none ++ rest)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fromRowErrCells_taken`
/-- The data loss: after a taken cell that is not the first, the row does not come back
    unchanged. -/
recall fromRowErrCells_taken_ne (vs ws : List value.Value) (rest : List (Option value.Value))
    (os : List (Option CellOutcome)) (h : ws.length = vs.length) (hne : vs ≠ []) :
    fromRowErrCells (vs.map some ++ none :: rest)
        (ws.map (fun w => some (.converted w)) ++ some .taken :: os) ≠
      some (vs.map some ++ none :: rest)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fromRowErrCells_taken_ne`
/-- `allCells` is every value exactly when no cell is empty. -/
recall allCells_eq_some_iff {α : Type} (cells : List (Option α)) (vs : List α) :
    allCells cells = some vs ↔ cells = vs.map some

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.allCells_eq_some_iff`
/-- The crate's `FromValue` impls use the default methods; e.g. `i64` and `String`. -/
recall defaultFromValue_i64 :
    DefaultFromValue I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.defaultFromValue_i64`
/-- The crate's `FromValue` impls use the default methods; e.g. `i64` and `String`. -/
recall defaultFromValue_string :
    DefaultFromValue alloc.string.String.Insts.Mysql_commonValueConvertFromValueString

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.defaultFromValue_string`
end Defs
