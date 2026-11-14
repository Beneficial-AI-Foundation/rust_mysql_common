import Defs
import Proofs.Util.RowAccess
import Proofs.Row.RowAccess
import Proofs.Row.ColumnIndexUsize

/-! Statements for `impl<T: FromValue> FromRow for T` (spec file: `Specs/Row/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open RowAccessUtil

private theorem usize_idx_proj :
    row.ColumnIndex.idx Usize.Insts.Mysql_commonRowColumnIndex =
      Usize.Insts.Mysql_commonRowColumnIndex.idx := rfl

private theorem blanket_one_pre {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (c : Option value.Value) (hr : r.values.val = [c]) (hcols : 1 ≤ r.columns.length) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r =
      (do
        let (o, r1) ← (match cellAt r.values.val 0 with
          | none => ok (none, r)
          | some v => do
            let x ← value.Value.Insts.Mysql_commonValueConvertFromValueValueIr.from_value v
            ok (some x, { r with values := r.values.set 0#usize none }))
        match o with
        | none => ok (core.result.Result.Err r1)
        | some v => do
          let r2 ← inst1.get_intermediate v
          match r2 with
          | .Ok ir => do
            let t ← inst1.coreconvertIntoInst.into ir
            ok (.Ok t)
          | .Err fve => do
            let r3 ← r1.place 0#usize fve
            ok (.Err r3)) := by
  have hl : alloc.vec.Vec.len r.values = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [hr]
  have h0 : (0#usize).val < r.columns.length := by simp; scalar_tac
  unfold row.convert.FromRow.Blanket.from_row_opt row.Row.len
  rw [bind_ok, ite_eq_left hl, row.Row.take_eq]
  rw [usize_idx_proj, Usize.Insts.Mysql_commonRowColumnIndex.idx_eq, ite_eq_left h0]
  simp only [bind_tc_ok]
  rfl

/-- `from_row_opt` on a row whose one cell was taken. -/
private theorem blanket_none {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (hr : r.values.val = [none]) (hcols : 1 ≤ r.columns.length) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Err r) := by
  rw [blanket_one_pre inst1 r _ hr hcols]
  simp [cellAt, hr]

/-- `from_row_opt` on a row whose one cell holds `v`. -/
private theorem blanket_some {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (v : value.Value) (hr : r.values.val = [some v]) (hcols : 1 ≤ r.columns.length) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r =
      (do
        let r2 ← inst1.get_intermediate v
        match r2 with
        | .Ok ir => do
          let t ← inst1.coreconvertIntoInst.into ir
          ok (.Ok t)
        | .Err fve => do
          let r3 ← row.Row.place { r with values := r.values.set 0#usize none } 0#usize fve
          ok (.Err r3)) := by
  rw [blanket_one_pre inst1 r _ hr hcols]
  simp [cellAt, hr, value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from,
    core.convert.IntoFrom.into, value.Value.Insts.CoreConvertFromValueIr.from]

/-- A row of one cell and no column: `take` finds nothing. -/
private theorem blanket_one_nocol {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (hr : r.values.length = 1) (hcols : r.columns.length = 0) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Err r) := by
  have hl : alloc.vec.Vec.len r.values = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [hr]
  have h0 : ¬ (0#usize).val < r.columns.length := by rw [hcols]; simp
  unfold row.convert.FromRow.Blanket.from_row_opt row.Row.len
  rw [bind_ok, ite_eq_left hl, row.Row.take_eq]
  rw [usize_idx_proj, Usize.Insts.Mysql_commonRowColumnIndex.idx_eq, ite_eq_right h0]
  simp

private theorem default_ok_iff {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (hd1 : DefaultFromValue inst1) (v1 : value.Value) (x1 : T1) :
    (∃ ir1 : I1, inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1) ↔
      inst1.from_value_opt v1 = ok (.Ok x1) := by
  obtain ⟨hg, hf⟩ := hd1
  rw [hf, hg]
  simp only [value.convert.FromValue.from_value_opt.default, value.convert.FromValue.get_intermediate.default]
  constructor
  · rintro ⟨ir1, h1, h2⟩
    simp [h1, h2]
  · intro h
    obtain ⟨a, ha, hk⟩ := bind_eq_ok_inv h
    rcases a with ir | e
    · obtain ⟨t, ht, htk⟩ := bind_eq_ok_inv hk
      simp at htk; subst htk
      exact ⟨ir, ha, ht⟩
    · simp at hk

/-- `FromRow for T` (`T: FromValue`): `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
theorem row.convert.FromRow.Blanket.from_row_eq {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1) :
    (row.convert.FromRow.Blanket inst1).from_row = row.convert.FromRow.from_row.default (row.convert.FromRow.Blanket inst1) := by
  rfl

/-- `FromRow for T` (`T: FromValue`): a row with other than 1 cell is handed back unchanged as the error. -/
theorem row.convert.FromRow.Blanket.from_row_opt_len {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (h : r.values.length ≠ 1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Err r) := by
  have hl : ¬ alloc.vec.Vec.len r.values = 1#usize := by
    intro he; apply h; have := congrArg UScalar.val he; simpa using this
  unfold row.convert.FromRow.Blanket.from_row_opt row.Row.len
  rw [bind_ok, ite_eq_right hl]

/-- `FromRow for T` (`T: FromValue`): when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the converted value. Assumes at least 1 column (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem row.convert.FromRow.Blanket.from_row_opt_ok {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (v1 : value.Value) (ir1 : I1) (x1 : T1)
    (hr : r.values.val = [some v1]) (hcols : 1 ≤ r.columns.length)
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Ok x1) := by
  rw [blanket_some inst1 r _ hr hcols]
  simp [hi1, hx1]

/-- `FromRow for T` (`T: FromValue`) (headline): the conversion succeeds with `x1` exactly when the row has exactly 1 cell and at least 1 column, no cell taken, and its value has an `Ok` intermediate that turns into `x1`. Exact, for any `FromValue` impls. -/
theorem row.convert.FromRow.Blanket.from_row_opt_ok_iff {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (x1 : T1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Ok x1) ↔
      1 ≤ r.columns.length ∧ ∃ (v1 : value.Value) (ir1 : I1), r.values.val = [some v1] ∧
        inst1.get_intermediate v1 = ok (.Ok ir1) ∧ inst1.coreconvertIntoInst.into ir1 = ok x1 := by
  constructor
  · intro h
    by_cases hlen : r.values.length = 1
    · obtain ⟨c, hc⟩ : ∃ c, r.values.val = [c] := by
        rcases hv : r.values.val with _ | ⟨c, _ | ⟨d, t⟩⟩ <;> simp_all
      by_cases hcols : 1 ≤ r.columns.length
      · refine ⟨hcols, ?_⟩
        rcases c with _ | v
        · rw [blanket_none inst1 r hc hcols] at h; simp at h
        · rw [blanket_some inst1 r v hc hcols] at h
          obtain ⟨a, ha, hk⟩ := bind_eq_ok_inv h
          rcases a with ir | e
          · obtain ⟨t, ht, htk⟩ := bind_eq_ok_inv hk
            simp at htk; subst htk
            exact ⟨v, ir, hc, ha, ht⟩
          · obtain ⟨t, ht, htk⟩ := bind_eq_ok_inv hk
            simp at htk
      · rw [blanket_one_nocol inst1 r hlen (by omega)] at h; simp at h
    · rw [row.convert.FromRow.Blanket.from_row_opt_len inst1 r hlen] at h; simp at h
  · rintro ⟨hcols, v1, ir1, hr, hi1, hx1⟩
    exact row.convert.FromRow.Blanket.from_row_opt_ok inst1 r v1 ir1 x1 hr hcols hi1 hx1

/-- `FromRow for T` (`T: FromValue`) (headline, through `from_value_opt`): for impls with the default `FromValue` methods (`DefaultFromValue`; all of the crate's), the conversion succeeds with `x1` exactly when the row has exactly 1 cell and at least 1 column, no cell taken, and it converts by `from_value_opt` to `x1`. -/
theorem row.convert.FromRow.Blanket.from_row_opt_ok_iff_default {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (hd1 : DefaultFromValue inst1)
    (r : row.Row) (x1 : T1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Ok x1) ↔
      1 ≤ r.columns.length ∧ ∃ v1 : value.Value, r.values.val = [some v1] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) := by
  rw [row.convert.FromRow.Blanket.from_row_opt_ok_iff]
  simp only [← default_ok_iff inst1 hd1]
  constructor
  · rintro ⟨h1, v1, ir1, h2, h3, h4⟩; exact ⟨h1, v1, h2, ir1, h3, h4⟩
  · rintro ⟨h1, v1, h2, ir1, h3, h4⟩; exact ⟨h1, v1, ir1, h2, h3, h4⟩

/-- `FromRow for T` (`T: FromValue`): on failure the row comes back as the error (`fromRowErrCells`), with the same columns: unchanged when the cell was taken, and with the cell holding the rejected value `e` (`FromValueError(e)`) when the column's `FromValue` rejects it. Assumes at least 1 column (`Row::take` finds cell `k` through the column count; rows built by the crate have one cell per column). -/
theorem row.convert.FromRow.Blanket.from_row_opt_err {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (c1 : Option value.Value) (hr : r.values.val = [c1])
    (hcols : 1 ≤ r.columns.length)
    (o1 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 noRollback c1 o1)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1] [o1] = some cells) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄ := by
  rcases o1 with _ | (_ | e | w | _) <;>
    simp [fromRowErrCells, errStop, CellOutcome.OfOpt, CellOutcome.Of, allCells] at h1 he
  · subst h1 he
    rw [blanket_none inst1 r hr hcols]; simp [hr]
  · obtain ⟨v, rfl, hv⟩ := h1
    subst he
    rw [blanket_some inst1 r v hr hcols]
    simp only [hv, bind_ok]
    step with row.Row.place_spec as ⟨r3, h3, h3c⟩
    refine ⟨r3, rfl, ?_, h3c⟩
    rw [h3]; simp [alloc.vec.Vec.set, hr]

end mysql_common
