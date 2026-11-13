import Defs

/-! Statements for `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value) :
    (TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11) := by
  sorry

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: a row with other than 12 cells is handed back unchanged as the error. -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (h : r.values.length ≠ 12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Err r) := by
  sorry

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. Assumes at least 12 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (ir10 : I10) (ir11 : I11) (ir12 : I12) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) (x12 : T12)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11, some v12]) (hcols : 12 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hi6 : inst6.get_intermediate v6 = ok (.Ok ir6))
    (hi7 : inst7.get_intermediate v7 = ok (.Ok ir7))
    (hi8 : inst8.get_intermediate v8 = ok (.Ok ir8))
    (hi9 : inst9.get_intermediate v9 = ok (.Ok ir9))
    (hi10 : inst10.get_intermediate v10 = ok (.Ok ir10))
    (hi11 : inst11.get_intermediate v11 = ok (.Ok ir11))
    (hi12 : inst12.get_intermediate v12 = ok (.Ok ir12))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6)
    (hx7 : inst7.coreconvertIntoInst.into ir7 = ok x7)
    (hx8 : inst8.coreconvertIntoInst.into ir8 = ok x8)
    (hx9 : inst9.coreconvertIntoInst.into ir9 = ok x9)
    (hx10 : inst10.coreconvertIntoInst.into ir10 = ok x10)
    (hx11 : inst11.coreconvertIntoInst.into ir11 = ok x11)
    (hx12 : inst12.coreconvertIntoInst.into ir12 = ok x12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)) := by
  sorry

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)` (headline): the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)` exactly when the row has exactly 12 cells and at least 12 columns, no cell taken, and each value has an `Ok` intermediate that turns into the corresponding component. Exact, for any `FromValue` impls. -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) (x12 : T12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)) ↔
      12 ≤ r.columns.length ∧ ∃ (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (ir10 : I10) (ir11 : I11) (ir12 : I12), r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11, some v12] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 ∧
        inst2.get_intermediate v2 = ok (.Ok ir2) ∧ inst2.coreconvertIntoInst.into ir2 = ok x2 ∧
        inst3.get_intermediate v3 = ok (.Ok ir3) ∧ inst3.coreconvertIntoInst.into ir3 = ok x3 ∧
        inst4.get_intermediate v4 = ok (.Ok ir4) ∧ inst4.coreconvertIntoInst.into ir4 = ok x4 ∧
        inst5.get_intermediate v5 = ok (.Ok ir5) ∧ inst5.coreconvertIntoInst.into ir5 = ok x5 ∧
        inst6.get_intermediate v6 = ok (.Ok ir6) ∧ inst6.coreconvertIntoInst.into ir6 = ok x6 ∧
        inst7.get_intermediate v7 = ok (.Ok ir7) ∧ inst7.coreconvertIntoInst.into ir7 = ok x7 ∧
        inst8.get_intermediate v8 = ok (.Ok ir8) ∧ inst8.coreconvertIntoInst.into ir8 = ok x8 ∧
        inst9.get_intermediate v9 = ok (.Ok ir9) ∧ inst9.coreconvertIntoInst.into ir9 = ok x9 ∧
        inst10.get_intermediate v10 = ok (.Ok ir10) ∧ inst10.coreconvertIntoInst.into ir10 = ok x10 ∧
        inst11.get_intermediate v11 = ok (.Ok ir11) ∧ inst11.coreconvertIntoInst.into ir11 = ok x11 ∧
        inst12.get_intermediate v12 = ok (.Ok ir12) ∧ inst12.coreconvertIntoInst.into ir12 = ok x12 := by
  sorry

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)` (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)` exactly when the row has exactly 12 cells and at least 12 columns, no cell taken, and each converts by `from_value_opt` to the corresponding component. -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff_default {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8) (hd9 : DefaultFromValue inst9) (hd10 : DefaultFromValue inst10) (hd11 : DefaultFromValue inst11) (hd12 : DefaultFromValue inst12)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) (x12 : T12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)) ↔
      12 ≤ r.columns.length ∧ ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11, some v12] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8) ∧ inst9.from_value_opt v9 = ok (.Ok x9) ∧ inst10.from_value_opt v10 = ok (.Ok x10) ∧ inst11.from_value_opt v11 = ok (.Ok x11) ∧ inst12.from_value_opt v12 = ok (.Ok x12) := by
  sorry

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest), and before a taken cell `passed` suffices (no rollback happens there). Assumes at least 12 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12])
    (hcols : 12 ≤ r.columns.length)
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 into6.into c6 o6)
    (h7 : CellOutcome.OfOpt inst7 into7.into c7 o7)
    (h8 : CellOutcome.OfOpt inst8 into8.into c8 o8)
    (h9 : CellOutcome.OfOpt inst9 into9.into c9 o9)
    (h10 : CellOutcome.OfOpt inst10 into10.into c10 o10)
    (h11 : CellOutcome.OfOpt inst11 into11.into c11 o11)
    (h12 : CellOutcome.OfOpt inst12 noRollback c12 o12)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12] [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] = some cells) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  sorry

end mysql_common
