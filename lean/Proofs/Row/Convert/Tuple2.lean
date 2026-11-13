import Defs
import Proofs.Util.RowTuples

/-! Statements for `impl FromRow for (T1, T2)` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FromRow for (T1, T2)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value) :
    (Pair.Insts.Mysql_commonRowConvertFromRow inst1 inst2 into1).from_row = row.convert.FromRow.from_row.default (Pair.Insts.Mysql_commonRowConvertFromRow inst1 inst2 into1) := by
  rfl

/-- `FromRow for (T1, T2)`: a row with other than 2 cells is handed back unchanged as the error. -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (h : r.values.length ≠ 2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Err r) := by
  simp_all [Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len]

/-- `FromRow for (T1, T2)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. Assumes at least 2 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (v1 v2 : value.Value) (ir1 : I1) (ir2 : I2) (x1 : T1) (x2 : T2)
    (hr : r.values.val = [some v1, some v2]) (hcols : 2 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Ok (x1, x2)) := by
  have hlt : ∀ k : Nat, k < 2 → k < r.columns.val.length := fun k hk => by scalar_tac
  simp_all [Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt, row.Row.len, RowTuples.take_eq_lt]

/-- `FromRow for (T1, T2)` (headline): the conversion succeeds with `(x1, x2)` exactly when the row has exactly 2 cells and at least 2 columns, no cell taken, and each value has an `Ok` intermediate that turns into the corresponding component. Exact, for any `FromValue` impls. -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (x1 : T1) (x2 : T2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Ok (x1, x2)) ↔
      2 ≤ r.columns.length ∧ ∃ (v1 v2 : value.Value) (ir1 : I1) (ir2 : I2), r.values.val = [some v1, some v2] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 ∧
        inst2.get_intermediate v2 = ok (.Ok ir2) ∧ inst2.coreconvertIntoInst.into ir2 = ok x2 := by
  constructor
  · intro h
    unfold Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt at h
    by_cases hl : r.values.val.length = 2
    swap; · simp_all [row.Row.len]
    obtain ⟨c1, c2, hr⟩ : ∃ c1 c2, r.values.val = [c1, c2] := by
      match hv : r.values.val, hl with
      | [c1, c2], _ => exact ⟨c1, c2, rfl⟩
    row_fwd_cell 0 c1 inst1
    row_fwd_cell 1 c2 inst2
    row_fwd_finish
  · rintro ⟨hcols, v1, v2, ir1, ir2, hr, hi1, hx1, hi2, hx2⟩
    exact Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok inst1 inst2 into1 r v1 v2 ir1 ir2 x1 x2 hr hcols hi1 hi2 hx1 hx2

/-- `FromRow for (T1, T2)` (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `(x1, x2)` exactly when the row has exactly 2 cells and at least 2 columns, no cell taken, and each converts by `from_value_opt` to the corresponding component. -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff_default {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2)
    (r : row.Row) (x1 : T1) (x2 : T2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Ok (x1, x2)) ↔
      2 ≤ r.columns.length ∧ ∃ v1 v2 : value.Value, r.values.val = [some v1, some v2] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) := by
  rw [Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff]
  simp only [RowTuples.from_value_opt_ok_iff hd1, RowTuples.from_value_opt_ok_iff hd2]
  constructor
  · rintro ⟨hc, v1, v2, ir1, ir2, hr, h1a, h1b, h2a, h2b⟩
    exact ⟨hc, v1, v2, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩⟩
  · rintro ⟨hc, v1, v2, hr, ⟨ir1, h1a, h1b⟩, ⟨ir2, h2a, h2b⟩⟩
    exact ⟨hc, v1, v2, ir1, ir2, hr, h1a, h1b, h2a, h2b⟩

/-- `FromRow for (T1, T2)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest), and before a taken cell `passed` suffices (no rollback happens there). Assumes at least 2 columns (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (c1 c2 : Option value.Value) (hr : r.values.val = [c1, c2])
    (hcols : 2 ≤ r.columns.length)
    (o1 o2 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 noRollback c2 o2)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2] [o1, o2] = some cells) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  have hlt : ∀ k : Nat, k < 2 → k < r.columns.val.length := fun k hk => by scalar_tac
  have hlv : ∀ k : Nat, k < 2 → k < r.values.val.length := fun k hk => by simp [hr]; omega
  unfold fromRowErrCells at he
  unfold Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt
  row_err_cell h1
  row_err_cell h2
  simp at he

private theorem gi_i64_int1 : ∃ ir, I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.get_intermediate
    (.Int 1#i64) = ok (.Ok ir) :=
  ⟨.Ready 1#i64, by
    simp [value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from, lift,
      I64.rMin, I64.rMax]⟩

private theorem gi_i8_uint5 : I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.get_intermediate
    (.UInt 5#u64) = ok (.Ok (.Ready 5#i8)) := by
  have : UScalar.hcast IScalarTy.I8 5#u64 = 5#i8 := by decide
  simp [value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from, lift,
    I8.rMax, this]

private theorem rollback_i8_5 :
    (core.convert.IntoFrom value.Value.Insts.CoreConvertFromParseIrOptI8).into (.Ready 5#i8) =
      ok (.Int 5#i64) := by
  simp [core.convert.IntoFrom.into, value.Value.Insts.CoreConvertFromParseIrOptI8.from,
    value.convert.ParseIrOpt.rollback, value.Value.Insts.CoreConvertFromI8.from, lift]
  decide

private theorem gi_string_int3 :
    alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.get_intermediate
      (.Int 3#i64) = ok (.Err (.Int 3#i64)) := by
  simp [alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- Upstream bug (data loss), `from_row_opt::<(i64, String)>`: the row `[Some(Int 1), None]`
    (the second value taken earlier) comes back as `[None, None]`: the `Int 1` taken out of the
    first cell is not put back, although the documentation promises the original row. -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_taken_loses_value (r : row.Row)
    (hr : r.values.val = [some (.Int 1#i64), none]) (hcols : 2 ≤ r.columns.length) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt
      I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64
      alloc.string.String.Insts.Mysql_commonValueConvertFromValueString
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromParseIrOptI64) r
      ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = [none, none] ∧
        r'.columns = r.columns ⦄ := by
  obtain ⟨ir, hg⟩ := gi_i64_int1
  exact Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err _ _ _ r _ _ hr hcols
    (some .passed) (some .taken) ⟨_, ir, rfl, hg⟩ rfl [none, none] rfl

/-- Upstream bug (rollback changes values), `from_row_opt::<(i8, String)>`: the row
    `[Some(UInt 5), Some(Int 3)]` comes back as `[Some(Int 5), Some(Int 3)]`: `String` rejects
    `Int 3`, and the first cell is put back as `Value::from` of the `i8` intermediate, which is
    `Int 5`, not the original `UInt 5`. -/
theorem Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_rollback_changes_value (r : row.Row)
    (hr : r.values.val = [some (.UInt 5#u64), some (.Int 3#i64)]) (hcols : 2 ≤ r.columns.length) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt
      I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8
      alloc.string.String.Insts.Mysql_commonValueConvertFromValueString
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromParseIrOptI8) r
      ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = [some (.Int 5#i64), some (.Int 3#i64)] ∧
        r'.columns = r.columns ⦄ := by
  exact Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err _ _ _ r _ _ hr hcols
    (some (.converted (.Int 5#i64))) (some (.rejected (.Int 3#i64)))
    ⟨_, _, rfl, gi_i8_uint5, rollback_i8_5⟩ ⟨_, rfl, gi_string_int3⟩ _ rfl

end mysql_common
