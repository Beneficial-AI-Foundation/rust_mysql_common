import Defs

/-! Statements for `ParsedNamedParams` (spec file: `Specs/NamedParams.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ParsedNamedParams::parse`: total and exact on any query, as the crate reads it
    (`crateLex`, the intended tokenizer with the crate's documented deviations). Never panics. -/
theorem named_params.ParsedNamedParams.parse_spec (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (crateLex q.val) r ⦄ := by
  sorry

/-- Headline: on a query without the lexical patterns the crate mis-reads (`QuirkFree`), `parse`
    is exactly the intended placeholder language: error iff named and positional placeholders
    are mixed; otherwise each named placeholder is replaced by `?` and the names are listed in
    order. -/
theorem named_params.ParsedNamedParams.parse_spec_intended (q : Slice U8) (h : QuirkFree q.val) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (sqlLex q.val) r ⦄ := by
  sorry

/-- On any query, the rewrite changes nothing but placeholders: the query is cut into pieces,
    the output replaces some pieces `:name` by `?` and copies the others, and the names returned
    are exactly those pieces' names, in order. -/
theorem named_params.ParsedNamedParams.parse_rewrite (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => ∀ p, r = .Ok p →
      ∃ ts : List Tok, ts.flatMap Tok.src = q.val ∧ cowList p.query = ts.flatMap Tok.out ∧
        p.params.val.map cowList = tokNames ts ⦄ := by
  sorry

/-- Quirk (deviation 3): a `?` right after a named placeholder is not seen, so mixing is not
    detected: `":a?"` gives the query `"??"` with the single name `a` (two markers, one
    parameter). -/
theorem named_params.ParsedNamedParams.parse_quirk_qmark_after_named (q : Slice U8)
    (h : q.val = ascii ":a?") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "??" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  sorry

/-- Quirk (deviation 1): the byte after a lone `-` is skipped, so `"1-:a"` has no placeholder
    and is returned unchanged. -/
theorem named_params.ParsedNamedParams.parse_quirk_after_minus (q : Slice U8)
    (h : q.val = ascii "1-:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "1-:a" ∧ p.params.val = [] ⦄ := by
  sorry

/-- Quirk (deviation 1): the quote after a lone `/` is skipped, so a placeholder inside the
    string literal of `"x/'a:b'"` is substituted: query `"x/'a?'"`, names `[b]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_after_slash (q : Slice U8)
    (h : q.val = ascii "x/'a:b'") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "x/'a?'" ∧ p.params.val.map cowList = [ascii "b"] ⦄ := by
  sorry

/-- Quirk (deviation 3): a `#` right after a named placeholder does not start a comment, so a
    placeholder in the comment is substituted: `":a#c\n:b"` gives `"?#c\n?"`, names `[a, b]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_comment_after_named (q : Slice U8)
    (h : q.val = ascii ":a#c\n:b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "?#c\n?" ∧ p.params.val.map cowList = [ascii "a", ascii "b"] ⦄ := by
  sorry

/-- Quirk (deviation 4): the empty comment `/**/` is not closed, so the rest of the query is a
    comment: `":a /**/ :b"` gives `"? /**/ :b"`, names `[a]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_empty_comment (q : Slice U8)
    (h : q.val = ascii ":a /**/ :b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "? /**/ :b" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  sorry

/-- Quirk (deviation 2): `--` followed by a vertical tab is a comment for MySQL but not for the
    crate: `"--\x0b:a"` gives `"--\x0b?"`, names `[a]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_dash_vtab (q : Slice U8)
    (h : q.val = ascii "--\x0b:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "--\x0b?" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  sorry

/-- `ParsedNamedParams::query`: the bytes of the (rewritten) query. -/
theorem named_params.ParsedNamedParams.impl.query_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.query p ⦃ s => s.val = cowList p.query ⦄ := by
  sorry

/-- `ParsedNamedParams::params`: the names, in order. -/
theorem named_params.ParsedNamedParams.impl.params_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.params p ⦃ s => s.val = p.params.val ⦄ := by
  sorry

end mysql_common
