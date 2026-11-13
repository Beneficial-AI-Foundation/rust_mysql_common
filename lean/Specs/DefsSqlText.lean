import Proofs.Defs.LemmasSqlText

/-!
# Facts about the SQL-text definitions (`lean/Defs/SqlText.lean`)
    Pure-Lean properties a signer should read: tokenizing loses nothing; on `QuirkFree` queries
    the crate's reading is the intended one; an example of the intended language; the server's
    reading inverts `quoteSql`; hex literals contain only hex digits; the name `into_values`
    reports is a missing one. Proofs: `Proofs/Defs/LemmasSqlText.lean`.

    **Trusted axioms:** none, except `intoValuesMissing_spec` (the `HashMap` model:
    `Trusted.paramsMapEntries`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ### Lemmas -/

/-- Tokenizing loses nothing: the tokens' bytes are the query (in both readings). -/
recall lex_src (crate : Bool) (q : List U8) : (lex crate q).flatMap Tok.src = q

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.lex_src`

/-- On a `QuirkFree` query the crate's reading is the intended one. -/
recall crateLex_eq_sqlLex (q : List U8) (h : QuirkFree q) : crateLex q = sqlLex q

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.crateLex_eq_sqlLex`

/-- An example of the intended language: placeholders in a quoted identifier, string literals
    (with `\"` and `''` escapes) and comments are not placeholders, and the query is
    `QuirkFree`. -/
recall sqlLex_example :
    let q := ascii "SELECT :a, `x:y`, \"q\\\":z\" FROM t /* :c */ WHERE x = 'it''s :c' AND y = :b -- :d\n# :e"
    QuirkFree q ∧ tokNames (sqlLex q) = [ascii "a", ascii "b"]

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sqlLex_example`

/-- The server reads `quoteSql nbe s` back as `s` (any bytes `s`), and the literal ends exactly
    at its last byte unless the following text starts with `'`. -/
recall sqlStrLit_quoteSql (nbe : Bool) (s rest : List U8)
    (hr : rest.head?.map (·.val) ≠ some 39) :
    sqlStrLit nbe (quoteSql nbe s ++ rest) = some (s, rest)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sqlStrLit_quoteSql`

/-- A hexadecimal literal contains only `0`, `x` and upper-case hex digits. -/
recall hexLit_chars (bs : List U8) :
    ∀ c ∈ hexLit bs, c ∈ ascii "0x0123456789ABCDEF"

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.hexLit_chars`

/-- The name `into_values` reports is one of the names, and has no value. -/
recall intoValuesMissing_spec (m : Trusted.ParamsMap) (names : List (List U8))
    (h : ∃ n ∈ names, Trusted.paramsMapLookup m n = none) :
    intoValuesMissing m names ∈ names ∧
      Trusted.paramsMapLookup m (intoValuesMissing m names) = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.intoValuesMissing_spec`

end Defs
