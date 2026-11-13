import Proofs.Defs.LemmasSqlText

/-!
# Facts about the SQL-text definitions (`lean/Defs/SqlText.lean`)
    Pure-Lean properties a signer should read: tokenizing loses nothing; on `QuirkFree` queries
    the crate's reading is the intended one; an example of the intended language; the server's
    reading inverts `quoteSql`, but not when quoted for the other `NO_BACKSLASH_ESCAPES` mode
    (an injection example in each direction); hex literals contain only hex digits; the name `into_values`
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

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.lex_src
/-- On a `QuirkFree` query the crate's reading is the intended one. -/
recall crateLex_eq_sqlLex (q : List U8) (h : QuirkFree q) : crateLex q = sqlLex q

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.crateLex_eq_sqlLex
/-- An example of the intended language: placeholders in a quoted identifier, string literals
    (with `\"` and `''` escapes) and comments are not placeholders, and the query is
    `QuirkFree`. -/
recall sqlLex_example :
    let q := ascii "SELECT :a, `x:y`, \"q\\\":z\" FROM t /* :c */ WHERE x = 'it''s :c' AND y = :b -- :d\n# :e"
    QuirkFree q ∧ tokNames (sqlLex q) = [ascii "a", ascii "b"]

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sqlLex_example
/-- The server reads `quoteSql nbe s` back as `s` (any bytes `s`), and the literal ends exactly
    at its last byte unless the following text starts with `'`. -/
recall sqlStrLit_quoteSql (nbe : Bool) (s rest : List U8)
    (hr : rest.head?.map (·.val) ≠ some 39) :
    sqlStrLit nbe (quoteSql nbe s ++ rest) = some (s, rest)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sqlStrLit_quoteSql
/-- **Mode mismatch** (security): `no_backslash_escape` must be the server's
    `NO_BACKSLASH_ESCAPES` mode. Quoted for one mode and read in the other, a value can end the
    literal early and inject SQL, in both directions. -/
recall sqlStrLit_mode_mismatch :
    sqlStrLit true (quoteSql false (ascii "x' OR 1=1 -- ")) =
      some (ascii "x\\", ascii " OR 1=1 -- '") ∧
    sqlStrLit false (quoteSql true (ascii "x\\' OR 1=1 -- ")) =
      some (ascii "x'", ascii " OR 1=1 -- '")

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sqlStrLit_mode_mismatch
/-- A hexadecimal literal contains only `0`, `x` and upper-case hex digits. -/
recall hexLit_chars (bs : List U8) :
    ∀ c ∈ hexLit bs, c ∈ ascii "0x0123456789ABCDEF"

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.hexLit_chars
/-- The name `into_values` reports is one of the names, and has no value. -/
recall intoValuesMissing_spec (m : Trusted.ParamsMap) (names : List (List U8))
    (h : ∃ n ∈ names, Trusted.paramsMapLookup m n = none) :
    intoValuesMissing m names ∈ names ∧
      Trusted.paramsMapLookup m (intoValuesMissing m names) = none

/-- [propext, Classical.choice, Quot.sound, Trusted.paramsMapEntries, std.hash.random.RandomState, std.collections.hash.map.HashMap] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.intoValuesMissing_spec
end Defs
