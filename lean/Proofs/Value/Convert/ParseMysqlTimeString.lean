import Defs

/-! Statements for `fn parse_mysql_time_string` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `parse_mysql_time_string` (private, used by the `Duration`, chrono and time conversions): on
    ASCII input, total; the text `TIME` literal `timeStringRead`, as `(negative, hours, minutes,
    seconds, microseconds)`. **ASCII hypothesis:** on non-ASCII input the Unicode-mode regexes
    can match non-ASCII digits and `btou(..).unwrap()` (or the padding loop's `6 - len`) panics,
    e.g. on `"00:00:00.\u{0660}"`; the regexes are only specified on ASCII input, so that case is
    excluded rather than stated. -/
theorem value.convert.parse_mysql_time_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_time_string b ⦃ r =>
      r.map (fun t => (t.1, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.val)) =
        timeStringRead b.val ⦄ := by
  sorry

end mysql_common
