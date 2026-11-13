import Defs

/-! Statements for `struct Row and its impls` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new_row_raw`: the row of the given cells and columns, when there are as many of each. -/
theorem row.new_row_raw_spec (values : alloc.vec.Vec (Option value.Value)) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length = columns.length) :
    row.new_row_raw values columns ⦃ r => r.values = values ∧ r.columns = columns ⦄ := by
  unfold row.new_row_raw
  simp [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, h]

/-- `new_row_raw` panics (`assert!`) when the numbers of cells and columns differ. -/
theorem row.new_row_raw_panics (values : alloc.vec.Vec (Option value.Value)) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length ≠ columns.length) :
    row.new_row_raw values columns = fail .assertionFailure := by
  unfold row.new_row_raw
  simp [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, h]

/-- `len`: the number of cells. -/
theorem row.Row.len_spec (self : row.Row) :
    row.Row.len self ⦃ n => n.val = self.values.length ⦄ := by
  unfold row.Row.len
  simp

/-- `is_empty`: no cells. -/
theorem row.Row.is_empty_spec (self : row.Row) :
    row.Row.is_empty self ⦃ b => (b ↔ self.values.val = []) ⦄ := by
  unfold row.Row.is_empty
  step*
  simp_all

/-- `columns_ref`: the columns. -/
theorem row.Row.columns_ref_eq (self : row.Row) :
    row.Row.columns_ref self = ok self.columns := by
  rfl

/-- `columns`: (another `Arc` to) the columns. -/
theorem row.Row.impl.columns_eq (self : row.Row) :
    row.Row.impl.columns self = ok self.columns := by
  rfl

/-- `unwrap_raw`: the cells. -/
theorem row.Row.unwrap_raw_eq (self : row.Row) :
    row.Row.unwrap_raw self = ok self.values := by
  rfl

end mysql_common
