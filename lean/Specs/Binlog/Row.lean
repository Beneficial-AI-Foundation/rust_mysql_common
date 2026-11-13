import Proofs.Binlog.Row.BinlogRowValueOptions
import Proofs.Binlog.Row.BinlogRow

/-!
# `src/binlog/row.rs`
    `BinlogRowValueOptions::try_from` and the `BinlogRow` accessors (`new`, `len`, `is_empty`,
    `columns_ref`, `columns`, `as_ref`, `take`, `unwrap`, `place`), as for `Row`
    (`Specs/Row.lean`).

    **Configuration.** As in `Specs/Binlog/Mod.lean`. `Arc<[Column]>` is modelled by its value
    (`TypesExternal.lean`), so `columns` (an `Arc` clone) is the columns themselves.

    **Patch.** Patch 151 writes `unwrap`'s `into_iter().map(..).collect()` as the recursive
    `unwrap_values`: stack use proportional to the number of values.

    **Definitions used.** `Defs/BinlogValue.lean` (`binlogCellAt`), `Defs/BinlogCore.lean`
    (`rowValueOptionsOfCode`), `Defs/RowConvert.lean` (`allCells`).

    **Trusted axioms.** None.

    **Not covered.** `MyDeserialize for BinlogRow` (needs the table map event's optional metadata
    iterators and `bitvec`; excluded in Cargo.toml), `TryFrom<BinlogRow> for Row` (excluded:
    JSONB to JSON through `serde_json`), `Debug`, derived `Clone`/`PartialEq`.

    **Behaviour to note.** `BinlogRowValueOptions` is an enum, not a flag word: only the exact
    value 1 (`PARTIAL_JSON_UPDATES`) converts. (The row deserializer itself tests the bit with
    `&`.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum BinlogRowValueOptions and its impls` -/

/-- `TryFrom<u64> for BinlogRowValueOptions`: total; `PARTIAL_JSON_UPDATES` for 1, else the value back as the error. -/
recall binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from_spec (value : U64) :
    binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from value =
      ok (match rowValueOptionsOfCode value.val with
        | some o => .Ok o
        | none => .Err value)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from_spec
/-! ### `struct BinlogRow and its impls` -/

/-- `new`: the row of the given cells and columns (no length check, unlike `Row`'s `new_row`). -/
recall binlog.row.BinlogRow.new_eq (values : alloc.vec.Vec (Option binlog.value.BinlogValue))
    (columns : alloc.sync.Arc (Slice packets.Column)) :
    binlog.row.BinlogRow.new values columns = ok { values, columns }

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.new_eq
/-- `len`: the number of cells. -/
recall binlog.row.BinlogRow.len_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.len self ⦃ n => n.val = self.values.length ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.len_spec
/-- `is_empty`: no cells. -/
recall binlog.row.BinlogRow.is_empty_spec (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.is_empty self ⦃ b => (b ↔ self.values.val = []) ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.is_empty_spec
/-- `columns_ref`: the columns. -/
recall binlog.row.BinlogRow.columns_ref_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.columns_ref self = ok self.columns

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.columns_ref_eq
/-- `columns`: (another `Arc` to) the columns. -/
recall binlog.row.BinlogRow.impl.columns_eq (self : binlog.row.BinlogRow) :
    binlog.row.BinlogRow.impl.columns self = ok self.columns

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.impl.columns_eq
/-- `as_ref`: the value in cell `index`, or `None` when there is no such cell or its value was taken. Never panics. -/
recall binlog.row.BinlogRow.as_ref_eq (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.as_ref self index = ok (binlogCellAt self.values.val index.val)

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.as_ref_eq
/-- `take`: the value in cell `index` (as `as_ref`), moved out: the cell is left empty (a missing cell: nothing changes), the columns unchanged. Never panics. -/
recall binlog.row.BinlogRow.take_spec (self : binlog.row.BinlogRow) (index : Usize) :
    binlog.row.BinlogRow.take self index ⦃ o r =>
      o = binlogCellAt self.values.val index.val ∧
        r.values.val = self.values.val.set index.val none ∧ r.columns = self.columns ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.take_spec
/-- `unwrap`: the values, in order, when no value was taken. -/
recall binlog.row.BinlogRow.unwrap_spec (self : binlog.row.BinlogRow) (vs : List binlog.value.BinlogValue)
    (h : allCells self.values.val = some vs) :
    binlog.row.BinlogRow.unwrap self ⦃ out => out.val = vs ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.unwrap_spec
/-- `unwrap` panics when some value was taken (documented). -/
recall binlog.row.BinlogRow.unwrap_panics (self : binlog.row.BinlogRow) (h : allCells self.values.val = none) :
    binlog.row.BinlogRow.unwrap self = fail .panic

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.unwrap_panics
/-- `place`: puts `value` in cell `index` (whether or not it was taken), the other cells and the columns unchanged. -/
recall binlog.row.BinlogRow.place_spec (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : index.val < self.values.length) :
    binlog.row.BinlogRow.place self index value ⦃ r =>
      r.values.val = self.values.val.set index.val (some value) ∧ r.columns = self.columns ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.place_spec
/-- `place` panics (index out of bounds) when there is no cell `index`. -/
recall binlog.row.BinlogRow.place_panics (self : binlog.row.BinlogRow) (index : Usize)
    (value : binlog.value.BinlogValue) (h : self.values.length ≤ index.val) :
    binlog.row.BinlogRow.place self index value = fail .arrayOutOfBounds

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.row.BinlogRow.place_panics
end mysql_common
