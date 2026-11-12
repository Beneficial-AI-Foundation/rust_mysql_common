import Defs

/-! Statements for `fn parse_mysql_datetime_string` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `parse_mysql_datetime_string` (private, used by the chrono conversions): on ASCII input,
    total; the text `DATE`/`DATETIME` literal `datetimeStringRead`. **ASCII hypothesis:** on
    non-ASCII input the Unicode-mode regexes can match non-ASCII digits and the following
    `btou(..).unwrap()` panics (e.g. `"2020-01-01 00:00:00.\u{0660}"`); the regexes are only
    specified on ASCII input, so that case is excluded rather than stated. -/
theorem value.convert.parse_mysql_datetime_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_datetime_string b ⦃ r =>
      r.map (fun t => (t.1.val, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.1.val,
        t.2.2.2.2.2.1.val, t.2.2.2.2.2.2.val)) = datetimeStringRead b.val ⦄ := by
  sorry

end mysql_common
