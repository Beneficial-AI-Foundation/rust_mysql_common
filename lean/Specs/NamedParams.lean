import Proofs.NamedParams.ParsedNamedParams

/-!
# `src/named_params.rs`
    `ParsedNamedParams::parse`, `query`, `params` (`MixedParamsError` is a unit struct, `Unit`
    in the translation; its derived `Clone`/`Eq`/`Debug` are not covered). Translated for real
    (patches 81–83: the loop body as `parse_step`, `is_ascii_whitespace` inlined, the
    substitution loop as a recursion `substitute_params` — more stack per named parameter).

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/SqlText.lean` (§1: `Tok`, `sqlLex` (intended language),
    `crateLex` (the crate's reading: the intended tokenizer with five documented deviations),
    `QuirkFree`, `parsedAs`, `ascii`), `Defs/Bytes.lean` (`cowList`).

    **Trusted axioms:** none. **Trusted models:** `Cow` `deref` (`FunsExternal.lean`, exact).

    **What is stated.** Exact and total: `parse` never panics and returns `parsedAs q
    (crateLex q)`. Headline: under `QuirkFree`, the intended placeholder language exactly
    (`Specs/DefsSqlText.lean`: `crateLex_eq_sqlLex`); on any query the rewrite only replaces
    `:name` pieces by `?` (`parse_rewrite`).

    **Behaviour to note (crate deviations from MySQL's lexical rules, `Defs/SqlText.lean` §1,
    with example theorems).** The state machine does not re-examine the byte after a lone `/`
    or `-`, after `--` not followed by tab/FF/CR/space, after a named placeholder or a lone `:`
    (unless it is `:`, `'` or `"`), nor the byte after `/*` and after each non-closing `*` in a
    comment; and it scans `/*+` optimizer hints as SQL. As a result: mixed `:a?` and `:a -?`
    are not reported (`parse_quirk_qmark_after_named`), placeholders after `-`/`/` are missed
    (`1-:a`, and right after the `*/` closing a `/*!` body) or found inside string literals
    (`x/'a:b'`), comments and quoted identifiers right after a placeholder are not recognised
    (`:a#c`), `/**/` and `/* x **/` swallow the rest of the query, and `/*+ hint :p */` has a
    placeholder. `/*! */` bodies are scanned for placeholders (as MySQL runs them).
    `sqlLex` is the reading under the **default `sql_mode`**: under `ANSI_QUOTES` (`"…"` is an
    identifier without backslash escapes: `"a\" :b "` has the placeholder `b`) or
    `NO_BACKSLASH_ESCAPES` (`\` ordinary in `'…'`) the placeholders can differ, and the crate
    does not know the mode.

    **Not covered:** derived `Clone`/`PartialEq`/`Debug` impls.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl ParsedNamedParams` -/

/-- `ParsedNamedParams::parse`: total and exact on any query, as the crate reads it
    (`crateLex`, the intended tokenizer with the crate's documented deviations). Never panics. -/
recall named_params.ParsedNamedParams.parse_spec (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (crateLex q.val) r ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_spec`

/-- Headline: on a query without the lexical patterns the crate mis-reads (`QuirkFree`), `parse`
    is exactly the intended placeholder language: error iff named and positional placeholders
    are mixed; otherwise each named placeholder is replaced by `?` and the names are listed in
    order. -/
recall named_params.ParsedNamedParams.parse_spec_intended (q : Slice U8) (h : QuirkFree q.val) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (sqlLex q.val) r ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_spec_intended`

/-- On any query, the rewrite changes nothing but placeholders: the query is cut into pieces,
    the output replaces some pieces `:name` by `?` and copies the others, and the names returned
    are exactly those pieces' names, in order. -/
recall named_params.ParsedNamedParams.parse_rewrite (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => ∀ p, r = .Ok p →
      ∃ ts : List Tok, ts.flatMap Tok.src = q.val ∧ cowList p.query = ts.flatMap Tok.out ∧
        p.params.val.map cowList = tokNames ts ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_rewrite`

/-- Quirk (deviation 3): a `?` right after a named placeholder is not seen, so mixing is not
    detected: `":a?"` gives the query `"??"` with the single name `a` (two markers, one
    parameter). -/
recall named_params.ParsedNamedParams.parse_quirk_qmark_after_named (q : Slice U8)
    (h : q.val = ascii ":a?") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "??" ∧ p.params.val.map cowList = [ascii "a"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_qmark_after_named`

/-- Quirk (deviation 1): the byte after a lone `-` is skipped, so `"1-:a"` has no placeholder
    and is returned unchanged. -/
recall named_params.ParsedNamedParams.parse_quirk_after_minus (q : Slice U8)
    (h : q.val = ascii "1-:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "1-:a" ∧ p.params.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_after_minus`

/-- Quirk (deviation 1): the quote after a lone `/` is skipped, so a placeholder inside the
    string literal of `"x/'a:b'"` is substituted: query `"x/'a?'"`, names `[b]`. -/
recall named_params.ParsedNamedParams.parse_quirk_after_slash (q : Slice U8)
    (h : q.val = ascii "x/'a:b'") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "x/'a?'" ∧ p.params.val.map cowList = [ascii "b"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_after_slash`

/-- Quirk (deviation 3): a `#` right after a named placeholder does not start a comment, so a
    placeholder in the comment is substituted: `":a#c\n:b"` gives `"?#c\n?"`, names `[a, b]`. -/
recall named_params.ParsedNamedParams.parse_quirk_comment_after_named (q : Slice U8)
    (h : q.val = ascii ":a#c\n:b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "?#c\n?" ∧ p.params.val.map cowList = [ascii "a", ascii "b"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_comment_after_named`

/-- Quirk (deviation 4): the empty comment `/**/` is not closed, so the rest of the query is a
    comment: `":a /**/ :b"` gives `"? /**/ :b"`, names `[a]`. -/
recall named_params.ParsedNamedParams.parse_quirk_empty_comment (q : Slice U8)
    (h : q.val = ascii ":a /**/ :b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "? /**/ :b" ∧ p.params.val.map cowList = [ascii "a"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_empty_comment`

/-- Quirk (deviation 2): `--` followed by a vertical tab is a comment for MySQL but not for the
    crate: `"--\x0b:a"` gives `"--\x0b?"`, names `[a]`. -/
recall named_params.ParsedNamedParams.parse_quirk_dash_vtab (q : Slice U8)
    (h : q.val = ascii "--\x0b:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "--\x0b?" ∧ p.params.val.map cowList = [ascii "a"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_dash_vtab`

/-- Quirk (deviation 5): an optimizer hint is scanned as SQL text, so `"/*+ h :p */"` gives
    `"/*+ h ? */"`, names `[p]` (MySQL never reads a hint body as SQL). -/
recall named_params.ParsedNamedParams.parse_quirk_hint (q : Slice U8)
    (h : q.val = ascii "/*+ h :p */") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "/*+ h ? */" ∧ p.params.val.map cowList = [ascii "p"] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.parse_quirk_hint`

/-- `ParsedNamedParams::query`: the bytes of the (rewritten) query. -/
recall named_params.ParsedNamedParams.impl.query_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.query p ⦃ s => s.val = cowList p.query ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.impl.query_spec`

/-- `ParsedNamedParams::params`: the names, in order. -/
recall named_params.ParsedNamedParams.impl.params_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.params p ⦃ s => s.val = p.params.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms named_params.ParsedNamedParams.impl.params_spec`

end mysql_common
