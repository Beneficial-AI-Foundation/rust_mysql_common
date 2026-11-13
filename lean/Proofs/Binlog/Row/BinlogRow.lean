import Defs

/-! Statements for `struct BinlogRow and its impls` (spec file: `Specs/Binlog/Row.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the row of the given cells and columns (no length check, unlike `Row`'s `new_row`). -/
theorem binlog.row.BinlogRow.new_eq (values : alloc.vec.Vec (Option binlog.value.BinlogValue))
    (columns : alloc.sync.Arc (Slice packets.Column)) :
    binlog.row.BinlogRow.new values columns = ok { values, columns } := by
  sorry

/-- `len`: the number of cells. -/
theorem binlog.row.BinlogRow.len_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.len self ⦃ n => n.val = self.values.length ⦄ := by
  sorry

/-- `is_empty`: no cells. -/
theorem binlog.row.BinlogRow.is_empty_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.is_empty self ⦃ b => (b ↔ self.values.val = []) ⦄ := by
  sorry

/-- `columns_ref`: the columns. -/
theorem binlog.row.BinlogRow.columns_ref_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.columns_ref self = ok self.columns := by
  sorry

/-- `columns`: (another `Arc` to) the columns. -/
theorem binlog.row.BinlogRow.impl.columns_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.impl.columns self = ok self.columns := by
  sorry

/-- `as_ref`: the value in cell `index`, or `None` when there is no such cell or its value was taken. Never panics. -/
theorem binlog.row.BinlogRow.as_ref_eq (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.as_ref self index = ok (binlogCellAt self.values.val index.val) := by
  sorry

/-- `take`: the value in cell `index` (as `as_ref`), moved out: the cell is left empty (a missing cell: nothing changes), the columns unchanged. Never panics. -/
theorem binlog.row.BinlogRow.take_spec (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.take self index ⦃ o r =>
      o = binlogCellAt self.values.val index.val ∧
        r.values.val = self.values.val.set index.val none ∧ r.columns = self.columns ⦄ := by
  sorry

/-- `unwrap`: the values, in order, when no value was taken. -/
theorem binlog.row.BinlogRow.unwrap_spec (self : binlog.row.BinlogRow) (vs : List binlog.value.BinlogValue)
    (h : allCells self.values.val = some vs) :
    binlog.row.BinlogRow.unwrap self ⦃ out => out.val = vs ⦄ := by
  sorry

/-- `unwrap` panics when some value was taken (documented). -/
theorem binlog.row.BinlogRow.unwrap_panics (self : binlog.row.BinlogRow) (h : allCells self.values.val = none) :
    binlog.row.BinlogRow.unwrap self = fail .panic := by
  sorry

/-- `place`: puts `value` in cell `index` (whether or not it was taken), the other cells and the columns unchanged. -/
theorem binlog.row.BinlogRow.place_spec (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : index.val < self.values.length) :
    binlog.row.BinlogRow.place self index value ⦃ r =>
      r.values.val = self.values.val.set index.val (some value) ∧ r.columns = self.columns ⦄ := by
  sorry

/-- `place` panics (index out of bounds) when there is no cell `index`. -/
theorem binlog.row.BinlogRow.place_panics (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : self.values.length ≤ index.val) :
    binlog.row.BinlogRow.place self index value = fail .arrayOutOfBounds := by
  sorry

end mysql_common
