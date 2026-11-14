import Defs
import Proofs.Util.RowTuples

/-! Statements for `impl FromRow for (T1, T2, T3, T4, T5, T6)` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) :
    (TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5) := by
  rfl

/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: a row with other than 6 cells is handed back unchanged as the error. -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (h : r.values.length ≠ 6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Err r) := by
  simp_all [TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len]

/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. Assumes at least 6 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6]) (hcols : 6 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hi6 : inst6.get_intermediate v6 = ok (.Ok ir6))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Ok (x1, x2, x3, x4, x5, x6)) := by
  have hlt : ∀ k : Nat, k < 6 → k < r.columns.val.length := fun k hk => by scalar_tac
  simp_all [TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len, RowTuples.take_eq_lt]

/-- `FromRow for (T1, T2, T3, T4, T5, T6)` (headline): the conversion succeeds with `(x1, x2, x3, x4, x5, x6)` exactly when the row has exactly 6 cells and at least 6 columns, no cell taken, and each value has an `Ok` intermediate that turns into the corresponding component. Exact, for any `FromValue` impls. -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Ok (x1, x2, x3, x4, x5, x6)) ↔
      6 ≤ r.columns.length ∧ ∃ (v1 v2 v3 v4 v5 v6 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6), r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 ∧
        inst2.get_intermediate v2 = ok (.Ok ir2) ∧ inst2.coreconvertIntoInst.into ir2 = ok x2 ∧
        inst3.get_intermediate v3 = ok (.Ok ir3) ∧ inst3.coreconvertIntoInst.into ir3 = ok x3 ∧
        inst4.get_intermediate v4 = ok (.Ok ir4) ∧ inst4.coreconvertIntoInst.into ir4 = ok x4 ∧
        inst5.get_intermediate v5 = ok (.Ok ir5) ∧ inst5.coreconvertIntoInst.into ir5 = ok x5 ∧
        inst6.get_intermediate v6 = ok (.Ok ir6) ∧ inst6.coreconvertIntoInst.into ir6 = ok x6 := by
  constructor
  · intro h
    unfold TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt at h
    by_cases hl : r.values.val.length = 6
    swap; · simp_all [row.Row.len]
    obtain ⟨c1, c2, c3, c4, c5, c6, hr⟩ : ∃ c1 c2 c3 c4 c5 c6, r.values.val = [c1, c2, c3, c4, c5, c6] := by
      match hv : r.values.val, hl with
      | [c1, c2, c3, c4, c5, c6], _ => exact ⟨c1, c2, c3, c4, c5, c6, rfl⟩
    row_fwd_cell 0 c1 inst1
    row_fwd_cell 1 c2 inst2
    row_fwd_cell 2 c3 inst3
    row_fwd_cell 3 c4 inst4
    row_fwd_cell 4 c5 inst5
    row_fwd_cell 5 c6 inst6
    row_fwd_finish
  · rintro ⟨hcols, v1, v2, v3, v4, v5, v6, ir1, ir2, ir3, ir4, ir5, ir6, hr, hi1, hx1, hi2, hx2, hi3, hx3, hi4, hx4, hi5, hx5, hi6, hx6⟩
    exact TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r v1 v2 v3 v4 v5 v6 ir1 ir2 ir3 ir4 ir5 ir6 x1 x2 x3 x4 x5 x6 hr hcols hi1 hi2 hi3 hi4 hi5 hi6 hx1 hx2 hx3 hx4 hx5 hx6

/-- `FromRow for (T1, T2, T3, T4, T5, T6)` (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6)` exactly when the row has exactly 6 cells and at least 6 columns, no cell taken, and each converts by `from_value_opt` to the corresponding component. -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff_default {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Ok (x1, x2, x3, x4, x5, x6)) ↔
      6 ≤ r.columns.length ∧ ∃ v1 v2 v3 v4 v5 v6 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) := by
  rw [TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff]
  simp only [RowTuples.from_value_opt_ok_iff hd1, RowTuples.from_value_opt_ok_iff hd2, RowTuples.from_value_opt_ok_iff hd3, RowTuples.from_value_opt_ok_iff hd4, RowTuples.from_value_opt_ok_iff hd5, RowTuples.from_value_opt_ok_iff hd6]
  constructor
  · rintro ⟨hc, v1, v2, v3, v4, v5, v6, ir1, ir2, ir3, ir4, ir5, ir6, hr, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, h5a, h5b, h6a, h6b⟩
    exact ⟨hc, v1, v2, v3, v4, v5, v6, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩, ⟨ir3, h3a, h3b⟩, ⟨ir4, h4a, h4b⟩, ⟨ir5, h5a, h5b⟩, ⟨ir6, h6a, h6b⟩⟩
  · rintro ⟨hc, v1, v2, v3, v4, v5, v6, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩, ⟨ir3, h3a, h3b⟩, ⟨ir4, h4a, h4b⟩, ⟨ir5, h5a, h5b⟩, ⟨ir6, h6a, h6b⟩⟩
    exact ⟨hc, v1, v2, v3, v4, v5, v6, ir1, ir2, ir3, ir4, ir5, ir6, hr, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, h5a, h5b, h6a, h6b⟩

/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest), and before a taken cell `passed` suffices (no rollback happens there). Assumes at least 6 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6])
    (hcols : 6 ≤ r.columns.length)
    (o1 o2 o3 o4 o5 o6 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 noRollback c6 o6)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6] [o1, o2, o3, o4, o5, o6] = some cells) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  have hlt : ∀ k : Nat, k < 6 → k < r.columns.val.length := fun k hk => by scalar_tac
  have hlv : ∀ k : Nat, k < 6 → k < r.values.val.length := fun k hk => by simp [hr]; omega
  unfold fromRowErrCells at he
  unfold TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt
  row_err_cell h1
  row_err_cell h2
  row_err_cell h3
  row_err_cell h4
  row_err_cell h5
  row_err_cell h6
  simp at he

end mysql_common
