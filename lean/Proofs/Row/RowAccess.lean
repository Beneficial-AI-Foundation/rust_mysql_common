import Defs

/-! Statements for the accessors of `struct Row` (`as_ref`, `get`, `get_opt`, `take`,
`take_opt`, `unwrap`, `place`; spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `as_ref`: the value in cell `index`, or `None` when there is no such cell or its value was
    taken. Never panics. -/
theorem row.Row.as_ref_eq (self : row.Row) (index : Usize) :
    row.Row.as_ref self index = ok (cellAt self.values.val index.val) := by
  sorry

/-- `get`: finds the column with the `ColumnIndex` impl; `None` when there is no such column, or
    its value was taken; otherwise converts a copy of the value with `from_value` (which panics
    when the value does not convert). The row is not changed (`&self`). -/
theorem row.Row.get_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (o : Option Usize) (hidx : ci.idx index self.columns = ok o) :
    row.Row.get inst ci self index =
      match cellAtIdx self.values.val o with
      | none => ok none
      | some v => inst.from_value v >>= fun x => ok (some x) := by
  sorry

/-- `get_opt`: as `get`, converting with `from_value_opt` (so a value that does not convert
    gives `Some(Err(..))` instead of a panic). -/
theorem row.Row.get_opt_eq {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (o : Option Usize) (hidx : ci.idx index self.columns = ok o) :
    row.Row.get_opt inst ci self index =
      match cellAtIdx self.values.val o with
      | none => ok none
      | some v => inst.from_value_opt v >>= fun x => ok (some x) := by
  sorry

/-- `take`: `None`, and the row unchanged, when there is no such column or its value was already
    taken. -/
theorem row.Row.take_none {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (o : Option Usize) (hidx : ci.idx index self.columns = ok o)
    (hc : cellAtIdx self.values.val o = none) :
    row.Row.take inst ci self index = ok (none, self) := by
  sorry

/-- `take`: moves the value out of cell `i` (leaving it empty, the columns unchanged) and
    returns it converted by `from_value`. -/
theorem row.Row.take_some {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (i : Usize) (hidx : ci.idx index self.columns = ok (some i))
    (v : value.Value) (hc : cellAt self.values.val i.val = some v) (x : T)
    (hx : inst.from_value v = ok x) :
    row.Row.take inst ci self index ⦃ y r =>
      y = some x ∧ r.values.val = self.values.val.set i.val none ∧ r.columns = self.columns ⦄ := by
  sorry

/-- `take`: fails exactly as `from_value` does on the value moved out (e.g. a panic when the
    value does not convert). -/
theorem row.Row.take_fail {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (i : Usize) (hidx : ci.idx index self.columns = ok (some i))
    (v : value.Value) (hc : cellAt self.values.val i.val = some v) (e : Error)
    (hx : inst.from_value v = fail e) :
    row.Row.take inst ci self index = fail e := by
  sorry

/-- `take_opt`: `None`, and the row unchanged, when there is no such column or its value was
    already taken. -/
theorem row.Row.take_opt_none {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (o : Option Usize) (hidx : ci.idx index self.columns = ok o)
    (hc : cellAtIdx self.values.val o = none) :
    row.Row.take_opt inst ci self index = ok (none, self) := by
  sorry

/-- `take_opt`: moves the value out of cell `i` (leaving it empty, the columns unchanged) and
    returns `from_value_opt` of it. The cell stays empty even when the value does not convert
    (the `FromValueError` holds the value). -/
theorem row.Row.take_opt_some {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (i : Usize) (hidx : ci.idx index self.columns = ok (some i))
    (v : value.Value) (hc : cellAt self.values.val i.val = some v)
    (res : core.result.Result T value.convert.FromValueError)
    (hx : inst.from_value_opt v = ok res) :
    row.Row.take_opt inst ci self index ⦃ y r =>
      y = some res ∧ r.values.val = self.values.val.set i.val none ∧ r.columns = self.columns ⦄ := by
  sorry

/-- `take_opt`: fails exactly as `from_value_opt` does on the value moved out. -/
theorem row.Row.take_opt_fail {T I Ix : Type} (inst : value.convert.FromValue T I) (ci : row.ColumnIndex Ix)
    (self : row.Row) (index : Ix) (i : Usize) (hidx : ci.idx index self.columns = ok (some i))
    (v : value.Value) (hc : cellAt self.values.val i.val = some v) (e : Error)
    (hx : inst.from_value_opt v = fail e) :
    row.Row.take_opt inst ci self index = fail e := by
  sorry

/-- `unwrap`: the values, in order, when no value was taken. -/
theorem row.Row.unwrap_spec (self : row.Row) (vs : List value.Value)
    (h : allCells self.values.val = some vs) :
    row.Row.unwrap self ⦃ out => out.val = vs ⦄ := by
  sorry

/-- `unwrap` panics when some value was taken. -/
theorem row.Row.unwrap_panics (self : row.Row) (h : allCells self.values.val = none) :
    row.Row.unwrap self = fail .panic := by
  sorry

/-- `place`: puts `v` in cell `index` (whether or not it was taken), the other cells and the
    columns unchanged. -/
theorem row.Row.place_spec (self : row.Row) (index : Usize) (v : value.Value)
    (h : index.val < self.values.length) :
    row.Row.place self index v ⦃ r =>
      r.values.val = self.values.val.set index.val (some v) ∧ r.columns = self.columns ⦄ := by
  sorry

/-- `place` panics (index out of bounds) when there is no cell `index`. -/
theorem row.Row.place_panics (self : row.Row) (index : Usize) (v : value.Value)
    (h : self.values.length ≤ index.val) :
    row.Row.place self index v = fail .arrayOutOfBounds := by
  sorry

end mysql_common
