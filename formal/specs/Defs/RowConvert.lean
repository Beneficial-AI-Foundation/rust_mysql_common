import Defs.Bytes
import Defs.Value

/-!
# Row access and row conversion: what they mean

The definitions the specs of the `Row` accessors (`src/row/mod.rs`) and of `FromRow`
(`src/row/convert/mod.rs`, `src/row/convert/frunk.rs`) are stated with. They are written from the
crate's documentation and the intended meaning, not from its code:

* **cells**: a row holds one cell per column; a cell is `none` once its value was taken out
  (`Row::take`). `cellAt` is the value in a cell, if there is one; `allCells` is every value,
  when none was taken. The crate keeps one cell per column (`RowWF`): `new_row`/`new_row_raw`
  assert it, the deserializers build rows that way, and `Row`'s fields are private. The Lean
  `row.Row` does not carry this invariant, so the conversion statements assume enough columns
  (`Row::take(k)` finds cell `k` through the column count: with fewer columns than cells a
  present cell behaves as taken).
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


/-- The crate's row invariant: one cell per column. Every row the crate builds has it
    (`new_row`/`new_row_raw` assert it, the deserializers build one value per column, and
    `Row`'s fields are private); `take` and `place` keep it. -/
def RowWF (r : row.Row) : Prop := r.columns.length = r.values.length

/-- What converting a row (`FromRow` for a tuple, or for `T: FromValue`) does at one cell, as far
    as the error is concerned:
    * `taken`: the cell is empty (its value was taken out earlier): the conversion fails;
    * `rejected e`: the column's `FromValue` rejects the value (`get_intermediate` is
      `Err(FromValueError(e))`): the conversion fails;
    * `converted w`: the value converts, and `w` is the `Value` its intermediate turns back into
      (`Into<Value>`), which is put back in the row if a later column fails;
    * `passed`: the value converts, without saying what its rollback gives (enough before a
      taken cell, where no rollback happens). -/
inductive CellOutcome where
  | taken
  | rejected (e : value.Value)
  | converted (w : value.Value)
  | passed

/-- `o` is what happens at cell `c` of a column converted by `inst`, whose intermediate turns
    back into a `Value` by `back`. -/
def CellOutcome.Of {T I : Type} (inst : value.convert.FromValue T I)
    (back : I → Result value.Value) (c : Option value.Value) : CellOutcome → Prop
  | .taken => c = none
  | .rejected e => ∃ v, c = some v ∧ inst.get_intermediate v = ok (.Err e)
  | .converted w => ∃ v ir, c = some v ∧ inst.get_intermediate v = ok (.Ok ir) ∧ back ir = ok w
  | .passed => ∃ v ir, c = some v ∧ inst.get_intermediate v = ok (.Ok ir)

/-- `CellOutcome.Of` for an optional outcome: `some o` says the outcome at the cell is `o`;
    `none` says nothing about the cell (no hypothesis; used for the cells after the first
    failure, which the conversion never reaches). -/
def CellOutcome.OfOpt {T I : Type} (inst : value.convert.FromValue T I)
    (back : I → Result value.Value) (c : Option value.Value) : Option CellOutcome → Prop
  | none => True
  | some o => CellOutcome.Of inst back c o

/-- The rollback of the last column of a tuple, which is never needed (no column after it can
    fail). Any function would do; this one is used so that `CellOutcome.Of` can be stated
    uniformly. With it, a `converted w` outcome of the last column forces `w = NULL`; that `w`
    is never used (if the last column converts, the conversion succeeds). -/
def noRollback {I : Type} : I → Result value.Value := fun _ => ok value.Value.NULL

/-- Where a row conversion stops, from the outcomes of its cells in column order: for each cell
    converted before the first failing cell, its rollback value if known (`converted w`) or
    `none` (`passed`), and how the failing cell fails (`none`: it was taken; `some e`: it was
    rejected with `e`). `none` when no cell fails, or when the outcome of a cell before the
    first failure is not described (`none`). -/
def errStop : List (Option CellOutcome) → Option (List (Option value.Value) × Option value.Value)
  | [] => none
  | none :: _ => none
  | some .taken :: _ => some ([], none)
  | some (.rejected e) :: _ => some ([], some e)
  | some (.converted w) :: os => (errStop os).map fun (ws, s) => (some w :: ws, s)
  | some .passed :: os => (errStop os).map fun (ws, s) => (none :: ws, s)

/-- The cells of the row a failed conversion hands back (`FromRowError`), given the row's cells
    and the outcomes at its cells, with `k` the first failing cell:
    * if cell `k` was taken: cells `0..k` are all empty, the cells after `k` are unchanged
      (the values converted before `k` are lost: the crate's behaviour, not a rollback);
    * if cell `k` was rejected with `e`: cells `0..k-1` hold the rollback values of their
      intermediates, cell `k` holds `e`, the cells after `k` are unchanged.
    `none` (nothing described) when no cell fails, when an outcome before the failure is not
    given, or when cell `k` is rejected and the rollback of an earlier cell is not given
    (`passed`). -/
def fromRowErrCells (cells : List (Option value.Value)) (outs : List (Option CellOutcome)) :
    Option (List (Option value.Value)) :=
  (errStop outs).bind fun (ws, s) =>
    match s with
    | none => some (List.replicate (ws.length + 1) none ++ cells.drop (ws.length + 1))
    | some e => (allCells ws).map fun vs => vs.map some ++ some e :: cells.drop (ws.length + 1)

end Defs
