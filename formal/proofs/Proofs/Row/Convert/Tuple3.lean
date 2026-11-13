import Defs
import Proofs.Util.RowTuples

/-! Statements for `impl FromRow for (T1, T2, T3)` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for (T1, T2, T3)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) :
    (TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 into1 into2).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 into1 into2) := by
  rfl

/-- `FromRow for (T1, T2, T3)`: a row with other than 3 cells is handed back unchanged as the error. -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (h : r.values.length ≠ 3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Err r) := by
  simp_all [TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len]

/-- `FromRow for (T1, T2, T3)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. Assumes at least 3 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (v1 v2 v3 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (x1 : T1) (x2 : T2) (x3 : T3)
    (hr : r.values.val = [some v1, some v2, some v3]) (hcols : 3 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Ok (x1, x2, x3)) := by
  have hlt : ∀ k : Nat, k < 3 → k < r.columns.val.length := fun k hk => by scalar_tac
  simp_all [TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len, RowTuples.take_eq_lt]

/-- `FromRow for (T1, T2, T3)` (headline): the conversion succeeds with `(x1, x2, x3)` exactly when the row has exactly 3 cells and at least 3 columns, no cell taken, and each value has an `Ok` intermediate that turns into the corresponding component. Exact, for any `FromValue` impls. -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Ok (x1, x2, x3)) ↔
      3 ≤ r.columns.length ∧ ∃ (v1 v2 v3 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3), r.values.val = [some v1, some v2, some v3] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 ∧
        inst2.get_intermediate v2 = ok (.Ok ir2) ∧ inst2.coreconvertIntoInst.into ir2 = ok x2 ∧
        inst3.get_intermediate v3 = ok (.Ok ir3) ∧ inst3.coreconvertIntoInst.into ir3 = ok x3 := by
  constructor
  · intro h
    unfold TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt at h
    by_cases hl : r.values.val.length = 3
    swap; · simp_all [row.Row.len]
    obtain ⟨c1, c2, c3, hr⟩ : ∃ c1 c2 c3, r.values.val = [c1, c2, c3] := by
      match hv : r.values.val, hl with
      | [c1, c2, c3], _ => exact ⟨c1, c2, c3, rfl⟩
    row_fwd_cell 0 c1 inst1
    row_fwd_cell 1 c2 inst2
    row_fwd_cell 2 c3 inst3
    row_fwd_finish
  · rintro ⟨hcols, v1, v2, v3, ir1, ir2, ir3, hr, hi1, hx1, hi2, hx2, hi3, hx3⟩
    exact TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok inst1 inst2 inst3 into1 into2 r v1 v2 v3 ir1 ir2 ir3 x1 x2 x3 hr hcols hi1 hi2 hi3 hx1 hx2 hx3

/-- `FromRow for (T1, T2, T3)` (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `(x1, x2, x3)` exactly when the row has exactly 3 cells and at least 3 columns, no cell taken, and each converts by `from_value_opt` to the corresponding component. -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff_default {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Ok (x1, x2, x3)) ↔
      3 ≤ r.columns.length ∧ ∃ v1 v2 v3 : value.Value, r.values.val = [some v1, some v2, some v3] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) := by
  rw [TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff]
  simp only [RowTuples.from_value_opt_ok_iff hd1, RowTuples.from_value_opt_ok_iff hd2, RowTuples.from_value_opt_ok_iff hd3]
  constructor
  · rintro ⟨hc, v1, v2, v3, ir1, ir2, ir3, hr, h1a, h1b, h2a, h2b, h3a, h3b⟩
    exact ⟨hc, v1, v2, v3, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩, ⟨ir3, h3a, h3b⟩⟩
  · rintro ⟨hc, v1, v2, v3, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩, ⟨ir3, h3a, h3b⟩⟩
    exact ⟨hc, v1, v2, v3, ir1, ir2, ir3, hr, h1a, h1b, h2a, h2b, h3a, h3b⟩

/-- `FromRow for (T1, T2, T3)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest), and before a taken cell `passed` suffices (no rollback happens there). Assumes at least 3 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (c1 c2 c3 : Option value.Value) (hr : r.values.val = [c1, c2, c3])
    (hcols : 3 ≤ r.columns.length)
    (o1 o2 o3 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 noRollback c3 o3)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3] [o1, o2, o3] = some cells) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  have hlt : ∀ k : Nat, k < 3 → k < r.columns.val.length := fun k hk => by scalar_tac
  have hlv : ∀ k : Nat, k < 3 → k < r.values.val.length := fun k hk => by simp [hr]; omega
  unfold fromRowErrCells at he
  unfold TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt
  row_err_cell h1
  row_err_cell h2
  row_err_cell h3
  simp at he

end mysql_common
