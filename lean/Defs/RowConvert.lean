import Defs.Bytes
import Defs.Value

/-!
# Row access and row conversion: what they mean

The definitions the specs of the `Row` accessors (`src/row/mod.rs`) and of `FromRow`
(`src/row/convert/mod.rs`, `src/row/convert/frunk.rs`) are stated with. They are written from the
crate's documentation and the intended meaning, not from its code:

* **cells**: a row holds one cell per column; a cell is `none` once its value was taken out
  (`Row::take`). `cellAt` is the value in a cell, if there is one; `allCells` is every value,
  when none was taken.
* **columns by name**: a column is found by its name, compared byte for byte (so
  case-sensitively); with duplicate names the first column wins (`colName`, `colIndexByName`).
* **converting a row** (`FromRow` for tuples, `T: FromValue`): column `k` is converted by the
  `k`-th type's `FromValue`. What happens at each cell is a `CellOutcome` (`CellOutcome.Of`);
  on failure, the row handed back in `FromRowError` is `fromRowErrCells`.

The crate documents that on failure `from_row_opt` "will roll back conversion and return
original row". `fromRowErrCells` describes what the crate actually returns, which differs:
* when a cell was already taken, the cells converted before it are **not** put back (they stay
  `none`): the row comes back with all cells up to that one empty;
* when a later column rejects its value, the earlier cells are put back as `Value::from` of
  their *intermediate*, which is the original value only if that conversion round-trips.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common

namespace Defs

/-! ## Cells -/

/-- The value in cell `i` of a row with cells `cells`: `none` when there is no cell `i` or its
    value was taken. -/
def cellAt (cells : List (Option value.Value)) (i : Nat) : Option value.Value :=
  match cells[i]? with
  | some (some v) => some v
  | _ => none

/-- The value a column index (`ColumnIndex::idx`, which gives `None` for no such column)
    designates in a row with cells `cells`: `none` when there is no such column or cell, or the
    value was taken. -/
def cellAtIdx (cells : List (Option value.Value)) : Option Usize → Option value.Value
  | none => none
  | some i => cellAt cells i.val

/-- Every value of a row, in order, when none was taken; `none` if some cell is empty. -/
def allCells {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some v :: cs => (allCells cs).map (v :: ·)

/-! ## Columns by name -/

/-- The name of a column, as bytes (the `name` field of its definition). -/
def colName (c : packets.Column) : List U8 := cowList c.«meta».«name».1

/-- The position of the first column named exactly `nm` (byte for byte, hence
    case-sensitive), if any. With duplicate names, the first. -/
def colIndexByName (nm : List U8) (cols : List packets.Column) : Option Nat :=
  cols.findIdx? (fun c => decide (colName c = nm))

/-! ## Converting a row -/

/-- Whether a `FromValue` impl uses the trait's default `get_intermediate` and `from_value_opt`
    (`try_from` of the intermediate, then `into`). Every impl in the crate does. -/
def DefaultFromValue {T I : Type} (inst : value.convert.FromValue T I) : Prop :=
  inst.get_intermediate = value.convert.FromValue.get_intermediate.default inst ∧
  inst.from_value_opt = value.convert.FromValue.from_value_opt.default inst

/-- What converting a row (`FromRow` for a tuple, or for `T: FromValue`) does at one cell, as far
    as the error is concerned:
    * `taken`: the cell is empty (its value was taken out earlier): the conversion fails;
    * `rejected e`: the column's `FromValue` rejects the value (`get_intermediate` is
      `Err(FromValueError(e))`): the conversion fails;
    * `converted w`: the value converts, and `w` is the `Value` its intermediate turns back into
      (`Into<Value>`), which is put back in the row if a later column fails. -/
inductive CellOutcome where
  | taken
  | rejected (e : value.Value)
  | converted (w : value.Value)

/-- `o` is what happens at cell `c` of a column converted by `inst`, whose intermediate turns
    back into a `Value` by `back`. -/
def CellOutcome.Of {T I : Type} (inst : value.convert.FromValue T I)
    (back : I → Result value.Value) (c : Option value.Value) : CellOutcome → Prop
  | .taken => c = none
  | .rejected e => ∃ v, c = some v ∧ inst.get_intermediate v = ok (.Err e)
  | .converted w => ∃ v ir, c = some v ∧ inst.get_intermediate v = ok (.Ok ir) ∧ back ir = ok w

/-- `CellOutcome.Of`, where `none` says nothing (the outcome at that cell is not described). -/
def CellOutcome.OfOpt {T I : Type} (inst : value.convert.FromValue T I)
    (back : I → Result value.Value) (c : Option value.Value) : Option CellOutcome → Prop
  | none => True
  | some o => CellOutcome.Of inst back c o

/-- The rollback of the last column of a tuple, which is never needed (no column after it can
    fail). Any function would do; this one is used so that `CellOutcome.Of` can be stated
    uniformly. -/
def noRollback {I : Type} : I → Result value.Value := fun _ => ok value.Value.NULL

/-- Where a row conversion stops, from the outcomes of its cells in column order: the rollback
    values of the cells converted before the first failing cell, and how that cell fails
    (`none`: it was taken; `some e`: it was rejected with `e`). `none` when no cell fails, or
    when the outcome of a cell before the first failure is not described (`none`). -/
def errStop : List (Option CellOutcome) → Option (List value.Value × Option value.Value)
  | [] => none
  | none :: _ => none
  | some .taken :: _ => some ([], none)
  | some (.rejected e) :: _ => some ([], some e)
  | some (.converted w) :: os => (errStop os).map fun (ws, s) => (w :: ws, s)

/-- The cells of the row a failed conversion hands back (`FromRowError`), given the row's cells
    and the outcomes at its cells (`none` when the conversion does not fail, as far as described):
    with `k` the first failing cell,
    * if cell `k` was taken: cells `0..k` are all empty, the cells after `k` are unchanged
      (the values converted before `k` are lost: the crate's behaviour, not a rollback);
    * if cell `k` was rejected with `e`: cells `0..k-1` hold the rollback values of their
      intermediates, cell `k` holds `e`, the cells after `k` are unchanged. -/
def fromRowErrCells (cells : List (Option value.Value)) (outs : List (Option CellOutcome)) :
    Option (List (Option value.Value)) :=
  (errStop outs).map fun (ws, s) =>
    match s with
    | none => List.replicate (ws.length + 1) none ++ cells.drop (ws.length + 1)
    | some e => ws.map some ++ some e :: cells.drop (ws.length + 1)

end Defs
