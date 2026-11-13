import Defs
import Proofs.Util.RowTuples

/-! Statements for `impl FromRow for (T1,)` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for (T1,)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1) :
    (TupleT1.Insts.Mysql_commonRowConvertFromRow inst1).from_row = row.convert.FromRow.from_row.default (TupleT1.Insts.Mysql_commonRowConvertFromRow inst1) := by
  rfl

/-- `FromRow for (T1,)`: a row with other than 1 cell is handed back unchanged as the error. -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (h : r.values.length ≠ 1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Err r) := by
  simp_all [TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len]

/-- `FromRow for (T1,)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the converted value. Assumes at least 1 column (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (v1 : value.Value) (ir1 : I1) (x1 : T1)
    (hr : r.values.val = [some v1]) (hcols : 1 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Ok x1) := by
  have hlt : ∀ k : Nat, k < 1 → k < r.columns.val.length := fun k hk => by scalar_tac
  simp_all [TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len, RowTuples.take_eq_lt]

/-- `FromRow for (T1,)` (headline): the conversion succeeds with `x1` exactly when the row has exactly 1 cell and at least 1 column, no cell taken, and its value has an `Ok` intermediate that turns into `x1`. Exact, for any `FromValue` impls. -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (x1 : T1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Ok x1) ↔
      1 ≤ r.columns.length ∧ ∃ (v1 : value.Value) (ir1 : I1), r.values.val = [some v1] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 := by
  constructor
  · intro h
    unfold TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt at h
    by_cases hl : r.values.val.length = 1
    swap; · simp_all [row.Row.len]
    obtain ⟨c1, hr⟩ : ∃ c1, r.values.val = [c1] := by
      match hv : r.values.val, hl with
      | [c1], _ => exact ⟨c1, rfl⟩
    row_fwd_cell 0 c1 inst1
    row_fwd_finish
  · rintro ⟨hcols, v1, ir1, hr, hi1, hx1⟩
    exact TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok inst1 r v1 ir1 x1 hr hcols hi1 hx1

/-- `FromRow for (T1,)` (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `x1` exactly when the row has exactly 1 cell and at least 1 column, no cell taken, and it converts by `from_value_opt` to `x1`. -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff_default {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (hd1 : DefaultFromValue inst1)
    (r : row.Row) (x1 : T1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Ok x1) ↔
      1 ≤ r.columns.length ∧ ∃ v1 : value.Value, r.values.val = [some v1] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) := by
  rw [TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff]
  simp only [RowTuples.from_value_opt_ok_iff hd1]
  constructor
  · rintro ⟨hc, v1, ir1, hr, h1a, h1b⟩
    exact ⟨hc, v1, hr, ⟨ir1, h1a, h1b⟩⟩
  · rintro ⟨hc, v1, hr, ⟨ir1, h1a, h1b⟩⟩
    exact ⟨hc, v1, ir1, hr, h1a, h1b⟩

/-- `FromRow for (T1,)`: on failure the row comes back as the error (`fromRowErrCells`), with the same columns: unchanged when the cell was taken, and with the cell holding the rejected value `e` (`FromValueError(e)`) when the column's `FromValue` rejects it. Assumes at least 1 column (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (c1 : Option value.Value) (hr : r.values.val = [c1])
    (hcols : 1 ≤ r.columns.length)
    (o1 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 noRollback c1 o1)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1] [o1] = some cells) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  have hlt : ∀ k : Nat, k < 1 → k < r.columns.val.length := fun k hk => by scalar_tac
  have hlv : ∀ k : Nat, k < 1 → k < r.values.val.length := fun k hk => by simp [hr]; omega
  unfold fromRowErrCells at he
  unfold TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt
  row_err_cell h1
  simp at he

end mysql_common
