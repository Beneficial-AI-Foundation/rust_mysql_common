import Defs

/-! Statements for `fn escaped` (private; used by `Value::as_sql`) (spec file:
`Specs/Value/AsSql.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `escaped(s, nbe)`: exactly the MySQL quoting `quoteSql nbe` of the bytes of `s`. (A Rust
    `&str` is always valid UTF-8; for a `Str` that is not, the final `from_utf8` would fail and
    this panics, which cannot happen from Rust.) -/
theorem value.escaped_spec (s : Str) (nbe : Bool) (h : IsUtf8 s.val) :
    value.escaped s nbe ⦃ r => utf8 r = quoteSql nbe s.val ⦄ := by
  sorry

end mysql_common
