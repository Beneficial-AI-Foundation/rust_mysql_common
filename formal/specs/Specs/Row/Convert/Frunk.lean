import Proofs.Row.Convert.Frunk.FromRowHNil

/-!
# `src/row/convert/frunk.rs`
    `FromRow` for frunk's heterogeneous lists: the empty list `HNil`.

    **Configuration.** As in `Specs/Io.lean`, with the `frunk` feature (enabled by
    `scripts/aeneas-translate.sh`). No statement needs `Target64`.

    **Patches.** 107 (the parameter `row` renamed).

    **Definitions used.** None beyond the translation (`row.Row`).

    **Trusted axioms.** None of the `Trusted.*` axioms.

    **Not covered.** `FromRow for HCons<H, T>` (not translated: it goes through frunk's
    `HList::LEN` and `h_cons`, which are not modelled).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl FromRow for HNil` -/

/-- `FromRow for HNil::from_row_opt`: `Ok(HNil)` for a row with no cells; any other row is
    handed back unchanged as the error. -/
recall frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq (r : row.Row) :
    frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_opt r =
      ok (if r.values.val = [] then .Ok () else .Err r)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_opt_eq
/-- `FromRow for HNil`: `from_row` is the trait's default (it panics exactly when
    `from_row_opt` is an `Err`, i.e. on a non-empty row). -/
recall frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_eq :
    frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row =
      row.convert.FromRow.from_row.default frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms frunk_core.hlist.HNil.Insts.Mysql_commonRowConvertFromRow.from_row_eq
end mysql_common
