import Defs

/-! Statements for `impl From<NaiveDateTime> for Value` (spec file: `Specs/Value/Convert/Chrono.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<NaiveDateTime> for Value`: for a year in `[1000, 9999]`, the `Date` of its fields
    (month, day, hour, minute, second taken mod 256 by `as u8`; nanoseconds truncated to
    microseconds). -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.from_spec (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x ⦃ w =>
      Val.ofValue w = match chronoDateTime x with
        | ((y, mo, d), (h, mi, s, ns)) =>
          .date y.toNat (mo % 256) (d % 256) (h % 256) (mi % 256) (s % 256) (ns / 1000) ⦄ := by
  sorry

/-- **Panic.** `From<NaiveDateTime> for Value` panics for a year outside `[1000, 9999]`. -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.from_panic (x : chrono.naive.datetime.NaiveDateTime) (hy : ¬ (1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)) :
    value.Value.Insts.CoreConvertFromNaiveDateTime.from x = fail .panic := by
  sorry

/-- Round trip: a valid date-time with a year in `[1000, 9999]` reads back with the same fields,
    nanoseconds truncated to microseconds. -/
theorem value.Value.Insts.CoreConvertFromNaiveDateTime.roundtrip (x : chrono.naive.datetime.NaiveDateTime) (hy : 1000 ≤ (chronoDateTime x).1.1 ∧ (chronoDateTime x).1.1 ≤ 9999)
    (hv : match chronoDateTime x with
      | ((y, mo, d), (h, mi, s, ns)) =>
        Trusted.chronoYmdValid y mo d ∧ Trusted.chronoHmsMicroValid h mi s (ns / 1000)) :
    (do let w ← value.Value.Insts.CoreConvertFromNaiveDateTime.from x; value.convert.from_value_opt chrono.naive.datetime.NaiveDateTime.Insts.Mysql_commonValueConvertFromValueParseIrNaiveDateTime w) ⦃ r =>
      ∃ x', r = .Ok x' ∧ chronoDateTime x' = match chronoDateTime x with
        | (dt, (h, mi, s, ns)) => (dt, (h, mi, s, ns / 1000 * 1000)) ⦄ := by
  sorry

end mysql_common
