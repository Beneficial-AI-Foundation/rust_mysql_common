import Proofs.Row.Convert.FreeFns
import Proofs.Row.Convert.FromRow
import Proofs.Row.Convert.FromRowRow
import Proofs.Row.Convert.FromRowBlanket
import Proofs.Row.Convert.Tuple1
import Proofs.Row.Convert.Tuple2
import Proofs.Row.Convert.Tuple3
import Proofs.Row.Convert.Tuple4
import Proofs.Row.Convert.Tuple5
import Proofs.Row.Convert.Tuple6
import Proofs.Row.Convert.Tuple7
import Proofs.Row.Convert.Tuple8
import Proofs.Row.Convert.Tuple9
import Proofs.Row.Convert.Tuple10
import Proofs.Row.Convert.Tuple11
import Proofs.Row.Convert.Tuple12

/-!
# `src/row/convert/mod.rs`
    Converting a `Row` to a Rust type (`FromRow`): the free functions `from_row`/`from_row_opt`,
    the trait's default `from_row`, and the impls for `Row`, for every `T: FromValue` (a one-column
    row), and for the tuples of arity 1 to 12.

    **How the impls are stated.** The tuple impls are generic in their component types: each
    statement takes the components' `FromValue` instances (and, for every component but the last,
    the `Into<Value>` of its intermediate, used for the rollback) as parameters, and describes the
    result in terms of what those instances return. Combine with the per-type statements of
    `Specs/Value/Convert*.lean` for concrete types. Every arity (1–12) gets the same five
    statements:
    * `from_row_eq`: `from_row` is the trait's default (panics iff `from_row_opt` is `Err`);
    * `from_row_opt_len`: a row of the wrong length comes back unchanged as the error;
    * `from_row_opt_ok`: every cell present and converting gives the tuple of the values;
    * `from_row_opt_ok_iff` (headline): for impls with the default `FromValue` methods
      (`DefaultFromValue`; every impl of the crate), `Ok(x1, .., xn)` exactly when the row has
      exactly `n` cells, none taken, and cell `k` converts by `from_value_opt` to `xk`;
    * `from_row_opt_err`: on failure, exactly which row comes back (`fromRowErrCells`).

    **Configuration.** As in `Specs/Io.lean` (x86_64-unknown-linux-gnu, the features of
    `scripts/aeneas-translate.sh`). No statement needs `Target64`.

    **Patches.** 105 (the panic message of `from_row` drops the row's `Debug` and the type name;
    the panic condition is the same), 106 (`start_from` attributes), 107 (renamed locals).

    **Definitions used.** `Defs/RowConvert.lean` (`DefaultFromValue`, `CellOutcome`,
    `CellOutcome.Of`, `CellOutcome.OfOpt`, `noRollback`, `errStop`, `fromRowErrCells`);
    facts about them in `Specs/DefsRowConvert.lean`.

    **Trusted axioms.** The generic statements rest on none of the `Trusted.*` axioms (the
    components' conversions are parameters). The two concrete bug statements use `i64`, `i8` and
    `String`, whose conversions are exact Lean definitions (no `Trusted` axiom).

    **Caveats.** Allocation is infallible in the model; overflow is a panic (debug semantics); the
    stack is not modelled. Panics inside a component's `get_intermediate` or `into` (e.g. the
    `Duration` parsers, README item 5) are not restated here: each statement assumes the
    component results it names, and a panicking component makes those hypotheses false.

    **Not covered.** `Display`/`Error for FromRowError` (formatting), the derived
    `Debug`/`Clone`/`PartialEq` of `FromRowError`; `FromRowError` itself is a plain wrapper of
    `Row` (`FromRowError := Row`) with nothing to state. The `nightly` bench.

    **Behaviour to note.**
    * **Data loss on a taken cell** (upstream bug). The documentation says `from_row_opt` "will
      roll back conversion and return original row". When a later cell was already taken
      (`Row::take`), the cells converted before it are not put back: `[Some(Int 1), None]` as
      `(i64, String)` comes back as `[None, None]` (`Pair…from_row_opt_taken_loses_value`).
    * **Rollback changes values** (upstream quirk, as README item 10). When a later column
      rejects its value, the earlier cells are put back as `Value::from` of their intermediate,
      which is the original only if the conversion round-trips: `[Some(UInt 5), Some(Int 3)]` as
      `(i8, String)` comes back as `[Some(Int 5), Some(Int 3)]`
      (`Pair…from_row_opt_rollback_changes_value`).
    * The rejected cell itself comes back as the value in its `FromValueError`, which for every
      crate impl is the original value (`Specs/Value/Convert.lean`).
    * A conversion of a row with any cell taken always fails, as documented.
    * `FromRow for Row` always succeeds, even on a row with taken cells.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `fn from_row`, `fn from_row_opt` -/

/-- `from_row`: the impl's `FromRow::from_row`. -/
recall row.convert.from_row_eq {T : Type} (inst : row.convert.FromRow T) (r : row.Row) :
    row.convert.from_row inst r = inst.from_row r

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.from_row_eq`
/-- `from_row_opt`: the impl's `FromRow::from_row_opt`. -/
recall row.convert.from_row_opt_eq {T : Type} (inst : row.convert.FromRow T) (r : row.Row) :
    row.convert.from_row_opt inst r = inst.from_row_opt r

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.from_row_opt_eq`
/-! ### `trait FromRow` -/

/-- `FromRow::from_row` (the default every impl but `Row`'s uses): when `from_row_opt` is
    `Ok x`, returns `x`. -/
recall row.convert.FromRow.from_row.default_ok {T : Type} (inst : row.convert.FromRow T) (r : row.Row) (x : T)
    (h : inst.from_row_opt r = ok (.Ok x)) :
    row.convert.FromRow.from_row.default inst r = ok x

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.from_row.default_ok`
/-- `FromRow::from_row` panics exactly when `from_row_opt` is an `Err`. (The panic message
    differs from upstream, patch 105; the condition is the same.) -/
recall row.convert.FromRow.from_row.default_panic {T : Type} (inst : row.convert.FromRow T) (r : row.Row)
    (e : row.convert.FromRowError) (h : inst.from_row_opt r = ok (.Err e)) :
    row.convert.FromRow.from_row.default inst r = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.from_row.default_panic`
/-! ### `impl FromRow for Row` -/

/-- `FromRow for Row::from_row`: the row itself; never panics. -/
recall row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_eq (r : row.Row) :
    row.Row.Insts.Mysql_commonRowConvertFromRow.from_row r = ok r

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for Row::from_row_opt`: the row itself, always `Ok` (even with taken cells). -/
recall row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq (r : row.Row) :
    row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_opt r = ok (.Ok r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq`
/-! ### `impl<T> FromRow for T where T: FromValue` -/

/-- `FromRow for T` (`T: FromValue`): `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall row.convert.FromRow.Blanket.from_row_eq {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1) :
    (row.convert.FromRow.Blanket inst1).from_row = row.convert.FromRow.from_row.default (row.convert.FromRow.Blanket inst1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.Blanket.from_row_eq`
/-- `FromRow for T` (`T: FromValue`): a row with other than 1 cell is handed back unchanged as the error. -/
recall row.convert.FromRow.Blanket.from_row_opt_len {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (h : r.values.length ≠ 1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.Blanket.from_row_opt_len`
/-- `FromRow for T` (`T: FromValue`): when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the converted value. -/
recall row.convert.FromRow.Blanket.from_row_opt_ok {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (v1 : value.Value) (ir1 : I1) (x1 : T1)
    (hr : r.values.val = [some v1])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Ok x1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.Blanket.from_row_opt_ok`
/-- `FromRow for T` (`T: FromValue`) (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `x1` exactly when the row has exactly 1 cell, none taken, and it converts by `from_value_opt` to `x1`. -/
recall row.convert.FromRow.Blanket.from_row_opt_ok_iff {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (hd1 : DefaultFromValue inst1)
    (r : row.Row) (x1 : T1) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r = ok (.Ok x1) ↔
      ∃ v1 : value.Value, r.values.val = [some v1] ∧
        inst1.from_value_opt v1 = ok (.Ok x1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.Blanket.from_row_opt_ok_iff`
/-- `FromRow for T` (`T: FromValue`): on failure the row comes back as the error (`fromRowErrCells`), with the same columns: unchanged when the cell was taken, and with the cell holding the rejected value `e` (`FromValueError(e)`) when the column's `FromValue` rejects it. -/
recall row.convert.FromRow.Blanket.from_row_opt_err {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (c1 : Option value.Value) (hr : r.values.val = [c1])
    (o1 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 noRollback c1 o1)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1] [o1] = some cells) :
    row.convert.FromRow.Blanket.from_row_opt inst1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms row.convert.FromRow.Blanket.from_row_opt_err`
/-! ### `impl FromRow for (T1,)` -/

/-- `FromRow for (T1,)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1) :
    (TupleT1.Insts.Mysql_commonRowConvertFromRow inst1).from_row = row.convert.FromRow.from_row.default (TupleT1.Insts.Mysql_commonRowConvertFromRow inst1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1,)`: a row with other than 1 cell is handed back unchanged as the error. -/
recall TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (h : r.values.length ≠ 1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1,)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the converted value. -/
recall TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (v1 : value.Value) (ir1 : I1) (x1 : T1)
    (hr : r.values.val = [some v1])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Ok x1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1,)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `x1` exactly when the row has exactly 1 cell, none taken, and it converts by `from_value_opt` to `x1`. -/
recall TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (hd1 : DefaultFromValue inst1)
    (r : row.Row) (x1 : T1) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r = ok (.Ok x1) ↔
      ∃ v1 : value.Value, r.values.val = [some v1] ∧
        inst1.from_value_opt v1 = ok (.Ok x1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1,)`: on failure the row comes back as the error (`fromRowErrCells`), with the same columns: unchanged when the cell was taken, and with the cell holding the rejected value `e` (`FromValueError(e)`) when the column's `FromValue` rejects it. -/
recall TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 I1 : Type} (inst1 : value.convert.FromValue T1 I1)
    (r : row.Row) (c1 : Option value.Value) (hr : r.values.val = [c1])
    (o1 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 noRollback c1 o1)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1] [o1] = some cells) :
    TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2)` -/

/-- `FromRow for (T1, T2)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value) :
    (Pair.Insts.Mysql_commonRowConvertFromRow inst1 inst2 into1).from_row = row.convert.FromRow.from_row.default (Pair.Insts.Mysql_commonRowConvertFromRow inst1 inst2 into1)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2)`: a row with other than 2 cells is handed back unchanged as the error. -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (h : r.values.length ≠ 2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (v1 v2 : value.Value) (ir1 : I1) (ir2 : I2) (x1 : T1) (x2 : T2)
    (hr : r.values.val = [some v1, some v2])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Ok (x1, x2))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2)` exactly when the row has exactly 2 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2)
    (r : row.Row) (x1 : T1) (x2 : T2) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r = ok (.Ok (x1, x2)) ↔
      ∃ v1 v2 : value.Value, r.values.val = [some v1, some v2] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 I1 I2 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2)
    (into1 : core.convert.Into I1 value.Value)
    (r : row.Row) (c1 c2 : Option value.Value) (hr : r.values.val = [c1, c2])
    (o1 o2 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 noRollback c2 o2)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2] [o1, o2] = some cells) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 into1 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-- Upstream bug (data loss), `from_row_opt::<(i64, String)>`: the row `[Some(Int 1), None]`
    (the second value taken earlier) comes back as `[None, None]`: the `Int 1` taken out of the
    first cell is not put back, although the documentation promises the original row. -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_taken_loses_value (r : row.Row)
    (hr : r.values.val = [some (.Int 1#i64), none]) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt
      I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64
      alloc.string.String.Insts.Mysql_commonValueConvertFromValueString
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromParseIrOptI64) r
      ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = [none, none] ∧
        r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_taken_loses_value`
/-- Upstream bug (rollback changes values), `from_row_opt::<(i8, String)>`: the row
    `[Some(UInt 5), Some(Int 3)]` comes back as `[Some(Int 5), Some(Int 3)]`: `String` rejects
    `Int 3`, and the first cell is put back as `Value::from` of the `i8` intermediate, which is
    `Int 5`, not the original `UInt 5`. -/
recall Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_rollback_changes_value (r : row.Row)
    (hr : r.values.val = [some (.UInt 5#u64), some (.Int 3#i64)]) :
    Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt
      I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8
      alloc.string.String.Insts.Mysql_commonValueConvertFromValueString
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromParseIrOptI8) r
      ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = [some (.Int 5#i64), some (.Int 3#i64)] ∧
        r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Pair.Insts.Mysql_commonRowConvertFromRow.from_row_opt_rollback_changes_value`
/-! ### `impl FromRow for (T1, T2, T3)` -/

/-- `FromRow for (T1, T2, T3)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) :
    (TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 into1 into2).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 into1 into2)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3)`: a row with other than 3 cells is handed back unchanged as the error. -/
recall TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (h : r.values.length ≠ 3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (v1 v2 v3 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (x1 : T1) (x2 : T2) (x3 : T3)
    (hr : r.values.val = [some v1, some v2, some v3])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Ok (x1, x2, x3))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3)` exactly when the row has exactly 3 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r = ok (.Ok (x1, x2, x3)) ↔
      ∃ v1 v2 v3 : value.Value, r.values.val = [some v1, some v2, some v3] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 I1 I2 I3 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value)
    (r : row.Row) (c1 c2 c3 : Option value.Value) (hr : r.values.val = [c1, c2, c3])
    (o1 o2 o3 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 noRollback c3 o3)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3] [o1, o2, o3] = some cells) :
    TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 into1 into2 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4)` -/

/-- `FromRow for (T1, T2, T3, T4)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 I1 I2 I3 I4 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) :
    (TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 into1 into2 into3).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 into1 into2 into3)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4)`: a row with other than 4 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 I1 I2 I3 I4 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value)
    (r : row.Row) (h : r.values.length ≠ 4) :
    TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 into1 into2 into3 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 I1 I2 I3 I4 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value)
    (r : row.Row) (v1 v2 v3 v4 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4)
    (hr : r.values.val = [some v1, some v2, some v3, some v4])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4) :
    TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 into1 into2 into3 r = ok (.Ok (x1, x2, x3, x4))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4)` exactly when the row has exactly 4 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 I1 I2 I3 I4 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) :
    TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 into1 into2 into3 r = ok (.Ok (x1, x2, x3, x4)) ↔
      ∃ v1 v2 v3 v4 : value.Value, r.values.val = [some v1, some v2, some v3, some v4] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 I1 I2 I3 I4 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value)
    (r : row.Row) (c1 c2 c3 c4 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4])
    (o1 o2 o3 o4 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 noRollback c4 o4)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4] [o1, o2, o3, o4] = some cells) :
    TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 into1 into2 into3 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5)` -/

/-- `FromRow for (T1, T2, T3, T4, T5)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 I1 I2 I3 I4 I5 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) :
    (TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5)`: a row with other than 5 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 I1 I2 I3 I4 I5 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value)
    (r : row.Row) (h : r.values.length ≠ 5) :
    TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 I1 I2 I3 I4 I5 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5) :
    TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4 r = ok (.Ok (x1, x2, x3, x4, x5))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5)` exactly when the row has exactly 5 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 I1 I2 I3 I4 I5 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) :
    TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4 r = ok (.Ok (x1, x2, x3, x4, x5)) ↔
      ∃ v1 v2 v3 v4 v5 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 I1 I2 I3 I4 I5 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5])
    (o1 o2 o3 o4 o5 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 noRollback c5 o5)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5] [o1, o2, o3, o4, o5] = some cells) :
    TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 into1 into2 into3 into4 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) :
    (TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: a row with other than 6 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (h : r.values.length ≠ 6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6])
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
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Ok (x1, x2, x3, x4, x5, x6))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6)` exactly when the row has exactly 6 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r = ok (.Ok (x1, x2, x3, x4, x5, x6)) ↔
      ∃ v1 v2 v3 v4 v5 v6 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 I1 I2 I3 I4 I5 I6 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6])
    (o1 o2 o3 o4 o5 o6 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 noRollback c6 o6)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6] [o1, o2, o3, o4, o5, o6] = some cells) :
    TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 into1 into2 into3 into4 into5 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 I1 I2 I3 I4 I5 I6 I7 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) :
    (TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7)`: a row with other than 7 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 I1 I2 I3 I4 I5 I6 I7 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value)
    (r : row.Row) (h : r.values.length ≠ 7) :
    TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 I1 I2 I3 I4 I5 I6 I7 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hi6 : inst6.get_intermediate v6 = ok (.Ok ir6))
    (hi7 : inst7.get_intermediate v7 = ok (.Ok ir7))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6)
    (hx7 : inst7.coreconvertIntoInst.into ir7 = ok x7) :
    TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7)` exactly when the row has exactly 7 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 I1 I2 I3 I4 I5 I6 I7 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) :
    TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 I1 I2 I3 I4 I5 I6 I7 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7])
    (o1 o2 o3 o4 o5 o6 o7 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 into6.into c6 o6)
    (h7 : CellOutcome.OfOpt inst7 noRollback c7 o7)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7] [o1, o2, o3, o4, o5, o6, o7] = some cells) :
    TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 into1 into2 into3 into4 into5 into6 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 I1 I2 I3 I4 I5 I6 I7 I8 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) :
    (TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)`: a row with other than 8 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 I1 I2 I3 I4 I5 I6 I7 I8 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value)
    (r : row.Row) (h : r.values.length ≠ 8) :
    TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 I1 I2 I3 I4 I5 I6 I7 I8 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hi6 : inst6.get_intermediate v6 = ok (.Ok ir6))
    (hi7 : inst7.get_intermediate v7 = ok (.Ok ir7))
    (hi8 : inst8.get_intermediate v8 = ok (.Ok ir8))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6)
    (hx7 : inst7.coreconvertIntoInst.into ir7 = ok x7)
    (hx8 : inst8.coreconvertIntoInst.into ir8 = ok x8) :
    TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8)` exactly when the row has exactly 8 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 I1 I2 I3 I4 I5 I6 I7 I8 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) :
    TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 I1 I2 I3 I4 I5 I6 I7 I8 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8])
    (o1 o2 o3 o4 o5 o6 o7 o8 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 into6.into c6 o6)
    (h7 : CellOutcome.OfOpt inst7 into7.into c7 o7)
    (h8 : CellOutcome.OfOpt inst8 noRollback c8 o8)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7, c8] [o1, o2, o3, o4, o5, o6, o7, o8] = some cells) :
    TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 into1 into2 into3 into4 into5 into6 into7 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 T9 I1 I2 I3 I4 I5 I6 I7 I8 I9 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) :
    (TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)`: a row with other than 9 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 T9 I1 I2 I3 I4 I5 I6 I7 I8 I9 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value)
    (r : row.Row) (h : r.values.length ≠ 9) :
    TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 T9 I1 I2 I3 I4 I5 I6 I7 I8 I9 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 v9 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9])
    (hi1 : inst1.get_intermediate v1 = ok (.Ok ir1))
    (hi2 : inst2.get_intermediate v2 = ok (.Ok ir2))
    (hi3 : inst3.get_intermediate v3 = ok (.Ok ir3))
    (hi4 : inst4.get_intermediate v4 = ok (.Ok ir4))
    (hi5 : inst5.get_intermediate v5 = ok (.Ok ir5))
    (hi6 : inst6.get_intermediate v6 = ok (.Ok ir6))
    (hi7 : inst7.get_intermediate v7 = ok (.Ok ir7))
    (hi8 : inst8.get_intermediate v8 = ok (.Ok ir8))
    (hi9 : inst9.get_intermediate v9 = ok (.Ok ir9))
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6)
    (hx7 : inst7.coreconvertIntoInst.into ir7 = ok x7)
    (hx8 : inst8.coreconvertIntoInst.into ir8 = ok x8)
    (hx9 : inst9.coreconvertIntoInst.into ir9 = ok x9) :
    TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9)` exactly when the row has exactly 9 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 T9 I1 I2 I3 I4 I5 I6 I7 I8 I9 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8) (hd9 : DefaultFromValue inst9)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) :
    TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8) ∧ inst9.from_value_opt v9 = ok (.Ok x9)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 T9 I1 I2 I3 I4 I5 I6 I7 I8 I9 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8, c9])
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 into6.into c6 o6)
    (h7 : CellOutcome.OfOpt inst7 into7.into c7 o7)
    (h8 : CellOutcome.OfOpt inst8 into8.into c8 o8)
    (h9 : CellOutcome.OfOpt inst9 noRollback c9 o9)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7, c8, c9] [o1, o2, o3, o4, o5, o6, o7, o8, o9] = some cells) :
    TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 into1 into2 into3 into4 into5 into6 into7 into8 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) :
    (TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)`: a row with other than 10 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value)
    (r : row.Row) (h : r.values.length ≠ 10) :
    TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (ir10 : I10) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10])
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
    (hx1 : inst1.coreconvertIntoInst.into ir1 = ok x1)
    (hx2 : inst2.coreconvertIntoInst.into ir2 = ok x2)
    (hx3 : inst3.coreconvertIntoInst.into ir3 = ok x3)
    (hx4 : inst4.coreconvertIntoInst.into ir4 = ok x4)
    (hx5 : inst5.coreconvertIntoInst.into ir5 = ok x5)
    (hx6 : inst6.coreconvertIntoInst.into ir6 = ok x6)
    (hx7 : inst7.coreconvertIntoInst.into ir7 = ok x7)
    (hx8 : inst8.coreconvertIntoInst.into ir8 = ok x8)
    (hx9 : inst9.coreconvertIntoInst.into ir9 = ok x9)
    (hx10 : inst10.coreconvertIntoInst.into ir10 = ok x10) :
    TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)` exactly when the row has exactly 10 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8) (hd9 : DefaultFromValue inst9) (hd10 : DefaultFromValue inst10)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) :
    TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8) ∧ inst9.from_value_opt v9 = ok (.Ok x9) ∧ inst10.from_value_opt v10 = ok (.Ok x10)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10])
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : Option CellOutcome)
    (h1 : CellOutcome.OfOpt inst1 into1.into c1 o1)
    (h2 : CellOutcome.OfOpt inst2 into2.into c2 o2)
    (h3 : CellOutcome.OfOpt inst3 into3.into c3 o3)
    (h4 : CellOutcome.OfOpt inst4 into4.into c4 o4)
    (h5 : CellOutcome.OfOpt inst5 into5.into c5 o5)
    (h6 : CellOutcome.OfOpt inst6 into6.into c6 o6)
    (h7 : CellOutcome.OfOpt inst7 into7.into c7 o7)
    (h8 : CellOutcome.OfOpt inst8 into8.into c8 o8)
    (h9 : CellOutcome.OfOpt inst9 into9.into c9 o9)
    (h10 : CellOutcome.OfOpt inst10 noRollback c10 o10)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10] = some cells) :
    TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 into1 into2 into3 into4 into5 into6 into7 into8 into9 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) :
    (TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)`: a row with other than 11 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value)
    (r : row.Row) (h : r.values.length ≠ 11) :
    TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (ir10 : I10) (ir11 : I11) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11])
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
    (hx11 : inst11.coreconvertIntoInst.into ir11 = ok x11) :
    TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)` exactly when the row has exactly 11 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8) (hd9 : DefaultFromValue inst9) (hd10 : DefaultFromValue inst10) (hd11 : DefaultFromValue inst11)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) :
    TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8) ∧ inst9.from_value_opt v9 = ok (.Ok x9) ∧ inst10.from_value_opt v10 = ok (.Ok x10) ∧ inst11.from_value_opt v11 = ok (.Ok x11)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11])
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Option CellOutcome)
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
    (h11 : CellOutcome.OfOpt inst11 noRollback c11 o11)
    (cells : List (Option value.Value)) (he : fromRowErrCells [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] = some cells) :
    TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
/-! ### `impl FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)` -/

/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: `from_row` is the trait's default (it panics exactly when `from_row_opt` is an `Err`, see `FromRow::from_row`). -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_eq {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value) :
    (TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11).from_row = row.convert.FromRow.from_row.default (TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_eq`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: a row with other than 12 cells is handed back unchanged as the error. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (h : r.values.length ≠ 12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Err r)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_len`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: when every cell holds a value whose column's intermediate is `Ok`, and every intermediate turns into the target type, the result is the tuple of the converted values, in column order. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : value.Value) (ir1 : I1) (ir2 : I2) (ir3 : I3) (ir4 : I4) (ir5 : I5) (ir6 : I6) (ir7 : I7) (ir8 : I8) (ir9 : I9) (ir10 : I10) (ir11 : I11) (ir12 : I12) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) (x12 : T12)
    (hr : r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11, some v12])
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
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)` (headline): for impls with the default `FromValue` methods (all of the crate's), the conversion succeeds with `(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)` exactly when the row has exactly 12 cells, none taken, and each converts by `from_value_opt` to the corresponding component. -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (hd1 : DefaultFromValue inst1) (hd2 : DefaultFromValue inst2) (hd3 : DefaultFromValue inst3) (hd4 : DefaultFromValue inst4) (hd5 : DefaultFromValue inst5) (hd6 : DefaultFromValue inst6) (hd7 : DefaultFromValue inst7) (hd8 : DefaultFromValue inst8) (hd9 : DefaultFromValue inst9) (hd10 : DefaultFromValue inst10) (hd11 : DefaultFromValue inst11) (hd12 : DefaultFromValue inst12)
    (r : row.Row) (x1 : T1) (x2 : T2) (x3 : T3) (x4 : T4) (x5 : T5) (x6 : T6) (x7 : T7) (x8 : T8) (x9 : T9) (x10 : T10) (x11 : T11) (x12 : T12) :
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r = ok (.Ok (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)) ↔
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : value.Value, r.values.val = [some v1, some v2, some v3, some v4, some v5, some v6, some v7, some v8, some v9, some v10, some v11, some v12] ∧
        inst1.from_value_opt v1 = ok (.Ok x1) ∧ inst2.from_value_opt v2 = ok (.Ok x2) ∧ inst3.from_value_opt v3 = ok (.Ok x3) ∧ inst4.from_value_opt v4 = ok (.Ok x4) ∧ inst5.from_value_opt v5 = ok (.Ok x5) ∧ inst6.from_value_opt v6 = ok (.Ok x6) ∧ inst7.from_value_opt v7 = ok (.Ok x7) ∧ inst8.from_value_opt v8 = ok (.Ok x8) ∧ inst9.from_value_opt v9 = ok (.Ok x9) ∧ inst10.from_value_opt v10 = ok (.Ok x10) ∧ inst11.from_value_opt v11 = ok (.Ok x11) ∧ inst12.from_value_opt v12 = ok (.Ok x12)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_ok_iff`
/-- `FromRow for (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12)`: on failure, exactly the row `fromRowErrCells` describes comes back as the error, with the same columns. Columns are converted left to right; at the first failing cell `k`: if it was taken, every cell up to `k` comes back empty (upstream data-loss bug: the cells converted before `k` are not put back, e.g. `[Some(Int 1), None]` as `(i64, String)` gives `[None, None]`); if its value is rejected, the cells before `k` come back as `Value::from` of their intermediates (the original value only when that conversion round-trips) and cell `k` as the rejected value. Only the outcomes up to the first failure need to be described (`none` for the rest). -/
recall TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 : Type} (inst1 : value.convert.FromValue T1 I1) (inst2 : value.convert.FromValue T2 I2) (inst3 : value.convert.FromValue T3 I3) (inst4 : value.convert.FromValue T4 I4) (inst5 : value.convert.FromValue T5 I5) (inst6 : value.convert.FromValue T6 I6) (inst7 : value.convert.FromValue T7 I7) (inst8 : value.convert.FromValue T8 I8) (inst9 : value.convert.FromValue T9 I9) (inst10 : value.convert.FromValue T10 I10) (inst11 : value.convert.FromValue T11 I11) (inst12 : value.convert.FromValue T12 I12)
    (into1 : core.convert.Into I1 value.Value) (into2 : core.convert.Into I2 value.Value) (into3 : core.convert.Into I3 value.Value) (into4 : core.convert.Into I4 value.Value) (into5 : core.convert.Into I5 value.Value) (into6 : core.convert.Into I6 value.Value) (into7 : core.convert.Into I7 value.Value) (into8 : core.convert.Into I8 value.Value) (into9 : core.convert.Into I9 value.Value) (into10 : core.convert.Into I10 value.Value) (into11 : core.convert.Into I11 value.Value)
    (r : row.Row) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : Option value.Value) (hr : r.values.val = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12])
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
    TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt inst1 inst2 inst3 inst4 inst5 inst6 inst7 inst8 inst9 inst10 inst11 inst12 into1 into2 into3 into4 into5 into6 into7 into8 into9 into10 into11 r ⦃ res => ∃ r' : row.Row, res = .Err r' ∧ r'.values.val = cells ∧ r'.columns = r.columns ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms TupleT1T2T3T4T5T6T7T8T9T10T11T12.Insts.Mysql_commonRowConvertFromRow.from_row_opt_err`
end mysql_common
