import Defs

/-! Facts about the SQL-text definitions (`lean/Defs/SqlText.lean`) (spec file:
`Specs/DefsSqlText.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- Tokenizing loses nothing: the tokens' bytes are the query (in both readings). -/
theorem lex_src (crate : Bool) (q : List U8) : (lex crate q).flatMap Tok.src = q := by
  sorry

/-- On a `QuirkFree` query the crate's reading is the intended one. -/
theorem crateLex_eq_sqlLex (q : List U8) (h : QuirkFree q) : crateLex q = sqlLex q := by
  sorry

/-- An example of the intended language: placeholders in a quoted identifier, string literals
    (with `\"` and `''` escapes) and comments are not placeholders, and the query is
    `QuirkFree`. -/
theorem sqlLex_example :
    let q := ascii "SELECT :a, `x:y`, \"q\\\":z\" FROM t /* :c */ WHERE x = 'it''s :c' AND y = :b -- :d\n# :e"
    QuirkFree q ∧ tokNames (sqlLex q) = [ascii "a", ascii "b"] := by
  sorry

/-- The server reads `quoteSql nbe s` back as `s` (any bytes `s`), and the literal ends exactly
    at its last byte unless the following text starts with `'`. -/
theorem sqlStrLit_quoteSql (nbe : Bool) (s rest : List U8)
    (hr : rest.head?.map (·.val) ≠ some 39) :
    sqlStrLit nbe (quoteSql nbe s ++ rest) = some (s, rest) := by
  sorry

/-- A hexadecimal literal contains only `0`, `x` and upper-case hex digits. -/
theorem hexLit_chars (bs : List U8) :
    ∀ c ∈ hexLit bs, c ∈ ascii "0x0123456789ABCDEF" := by
  sorry

/-- The name `into_values` reports is one of the names, and has no value. -/
theorem intoValuesMissing_spec (m : Trusted.ParamsMap) (names : List (List U8))
    (h : ∃ n ∈ names, Trusted.paramsMapLookup m n = none) :
    intoValuesMissing m names ∈ names ∧
      Trusted.paramsMapLookup m (intoValuesMissing m names) = none := by
  sorry

end Defs
