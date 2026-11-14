import Defs
import Proofs.Util.NamedParams
import Proofs.Util.RawBytesSeq
import Proofs.Defs.LemmasSqlText

/-! Statements for `ParsedNamedParams` (spec file: `Specs/NamedParams.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem flatMap_out_of_noNames : ∀ ts : List Tok, tokNames ts = [] →
    ts.flatMap Tok.out = ts.flatMap Tok.src
  | [], _ => rfl
  | .named n :: ts, h => by simp [tokNames_cons_named] at h
  | .qmark :: ts, h => by
    rw [tokNames_cons_other _ _ (by simp)] at h; simp [Tok.out, flatMap_out_of_noNames ts h]
  | .plain c :: ts, h => by
    rw [tokNames_cons_other _ _ (by simp)] at h; simp [Tok.out, flatMap_out_of_noNames ts h]
  | .skip c :: ts, h => by
    rw [tokNames_cons_other _ _ (by simp)] at h; simp [Tok.out, flatMap_out_of_noNames ts h]

/-- The loop and the fix-up: the crate's tokens. -/
private theorem parse_loop_fin (q : Slice U8) :
    named_params.ParsedNamedParams.parse_loop q .TopLevel false 0#usize
      (alloc.vec.Vec.new (Usize × Usize × Usize)) 0#usize ⦃ R =>
      R.2.1 = tokHasQmark (crateLex q.val) ∧
      pfin R.1 R.2.2.1.val (toN R.2.2.2.val) q.length = trip (crateLex q.val) 0 ∧
      pInv R.1 R.2.2.1.val R.2.2.2.length q.length ⦄ := by
  apply WP.spec_mono (parse_loop_spec q q.val .TopLevel false 0#usize
    (alloc.vec.Vec.new (Usize × Usize × Usize)) 0#usize (by simp) (by simp)
    (by simp [pInv]))
  intro R hR
  obtain ⟨hR1, hR2⟩ := hR
  have hE := E_top q.length q.val (by simp [Slice.length]) false [] 0
  simp only [List.length_nil, Bool.false_or, List.nil_append] at hE
  simp only [E] at hE
  change _ = prun .TopLevel false 0 [] 0 q.val at hR1
  rw [← hR1] at hE
  simp only [Prod.mk.injEq] at hE
  refine ⟨hE.1, ?_, hR2⟩
  rw [← hE.2]; simp [Slice.length, toN]

/-- `ParsedNamedParams::parse`: total and exact on any query, as the crate reads it
    (`crateLex`, the intended tokenizer with the crate's documented deviations). Never panics. -/
theorem named_params.ParsedNamedParams.parse_spec (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (crateLex q.val) r ⦄ := by
  unfold named_params.ParsedNamedParams.parse
  apply WP.spec_bind (parse_loop_fin q)
  rintro ⟨st, hp, cur, ps⟩ ⟨hhp, hfin, hinv⟩
  simp only at hhp hfin hinv
  cases st
  all_goals first
  | (have hcur := hinv.1 rfl
     step as ⟨x, hx1, hx2⟩
     obtain ⟨⟨a1, a2, a3⟩, back⟩ := x
     simp only at hx1 hx2 ⊢
     subst hx2
     have hlen : (q.len).val = q.length := rfl
     have hget : (toN ps.val)[cur.val]! = (a1.val, a2.val, a3.val) := by
       rw [toN, List.getElem!_eq_getElem?_getD, List.getElem?_map,
         List.getElem?_eq_getElem (by simpa using hcur), ← hx1]; rfl
     simp only [pfin, hget] at hfin
     have hP1 : toN (ps.set cur (a1, a2, q.len)).val = trip (crateLex q.val) 0 := by
       rw [← hfin]; simp [toN, List.map_set, hlen]
     clear hfin hget hx1 hinv
     apply WP.spec_bind (m := ok (ps.set cur (a1, a2, q.len))) ((WP.spec_ok _).mpr rfl)
     intro v hv
     rw [hv] at hP1
     clear hv)
  | (simp only [pfin] at hfin
     simp only
     clear hinv
     revert hfin
     generalize ps = v
     intro hP1)
  all_goals
    step as ⟨b, hb⟩
    have hlenv : v.length = (tokNames (crateLex q.val)).length := by
      have := congrArg List.length hP1; simp only [toN, List.length_map, trip_length] at this
      exact this
    split_ifs with hbt hpt
    · have hn : tokNames (crateLex q.val) = [] := by
        rw [← List.length_eq_zero_iff, ← hlenv]; exact cast hb hbt
      simp [parsedAs, hn, cowList, flatMap_out_of_noNames _ hn, lex_src, alloc.vec.Vec.new]
    · have hn : tokNames (crateLex q.val) ≠ [] := by
        rw [ne_eq, ← List.length_eq_zero_iff, ← hlenv]; exact fun h => hbt (cast hb.symm h)
      simp_all [parsedAs]
    · have hn : tokNames (crateLex q.val) ≠ [] := by
        rw [ne_eq, ← List.length_eq_zero_iff, ← hlenv]; exact fun h => hbt (cast hb.symm h)
      apply WP.spec_bind (substitute_spec q _ (crateLex q.val) [] _ _ _ _ (by simp [lex_src])
        (by simpa [alloc.vec.Vec.deref] using hP1) (by simp)
        (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
        (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]))
      rintro ⟨rq, op⟩ ⟨h1, h2⟩
      simp_all [parsedAs, cowList, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]

/-- Headline: on a query without the lexical patterns the crate mis-reads (`QuirkFree`), `parse`
    is exactly the intended placeholder language: error iff named and positional placeholders
    are mixed; otherwise each named placeholder is replaced by `?` and the names are listed in
    order. -/
theorem named_params.ParsedNamedParams.parse_spec_intended (q : Slice U8) (h : QuirkFree q.val) :
    named_params.ParsedNamedParams.parse q ⦃ r => parsedAs q (sqlLex q.val) r ⦄ := by
  rw [← crateLex_eq_sqlLex q.val h]
  exact named_params.ParsedNamedParams.parse_spec q

/-- On any query, the rewrite changes nothing but placeholders: the query is cut into pieces,
    the output replaces some pieces `:name` by `?` and copies the others, and the names returned
    are exactly those pieces' names, in order. -/
theorem named_params.ParsedNamedParams.parse_rewrite (q : Slice U8) :
    named_params.ParsedNamedParams.parse q ⦃ r => ∀ p, r = .Ok p →
      ∃ ts : List Tok, ts.flatMap Tok.src = q.val ∧ cowList p.query = ts.flatMap Tok.out ∧
        p.params.val.map cowList = tokNames ts ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr p hp
  subst hp
  exact ⟨crateLex q.val, lex_src true q.val, hr.2.1, hr.2.2.1⟩

/-- Quirk (deviation 3): a `?` right after a named placeholder is not seen, so mixing is not
    detected: `":a?"` gives the query `"??"` with the single name `a` (two markers, one
    parameter). -/
theorem named_params.ParsedNamedParams.parse_quirk_qmark_after_named (q : Slice U8)
    (h : q.val = ascii ":a?") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "??" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 1): the byte after a lone `-` is skipped, so `"1-:a"` has no placeholder
    and is returned unchanged. -/
theorem named_params.ParsedNamedParams.parse_quirk_after_minus (q : Slice U8)
    (h : q.val = ascii "1-:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "1-:a" ∧ p.params.val = [] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [← List.map_eq_nil_iff (f := cowList), h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 1): the quote after a lone `/` is skipped, so a placeholder inside the
    string literal of `"x/'a:b'"` is substituted: query `"x/'a?'"`, names `[b]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_after_slash (q : Slice U8)
    (h : q.val = ascii "x/'a:b'") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "x/'a?'" ∧ p.params.val.map cowList = [ascii "b"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 3): a `#` right after a named placeholder does not start a comment, so a
    placeholder in the comment is substituted: `":a#c\n:b"` gives `"?#c\n?"`, names `[a, b]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_comment_after_named (q : Slice U8)
    (h : q.val = ascii ":a#c\n:b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "?#c\n?" ∧ p.params.val.map cowList = [ascii "a", ascii "b"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 4): the empty comment `/**/` is not closed, so the rest of the query is a
    comment: `":a /**/ :b"` gives `"? /**/ :b"`, names `[a]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_empty_comment (q : Slice U8)
    (h : q.val = ascii ":a /**/ :b") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "? /**/ :b" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 2): `--` followed by a vertical tab is a comment for MySQL but not for the
    crate: `"--\x0b:a"` gives `"--\x0b?"`, names `[a]`. -/
theorem named_params.ParsedNamedParams.parse_quirk_dash_vtab (q : Slice U8)
    (h : q.val = ascii "--\x0b:a") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "--\x0b?" ∧ p.params.val.map cowList = [ascii "a"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- Quirk (deviation 5): an optimizer hint is scanned as SQL text, so `"/*+ h :p */"` gives
    `"/*+ h ? */"`, names `[p]` (MySQL never reads a hint body as SQL). -/
theorem named_params.ParsedNamedParams.parse_quirk_hint (q : Slice U8)
    (h : q.val = ascii "/*+ h :p */") :
    named_params.ParsedNamedParams.parse q ⦃ r => ∃ p, r = .Ok p ∧
      cowList p.query = ascii "/*+ h ? */" ∧ p.params.val.map cowList = [ascii "p"] ⦄ := by
  apply WP.spec_mono (named_params.ParsedNamedParams.parse_spec q)
  intro r hr
  rw [h] at hr
  rcases r with p | e
  · obtain ⟨_, h1, h2, _⟩ := hr
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [h1]; decide
    · rw [h2]; decide
  · exfalso; obtain ⟨_, h2⟩ := hr; revert h2; decide

/-- `ParsedNamedParams::query`: the bytes of the (rewritten) query. -/
theorem named_params.ParsedNamedParams.impl.query_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.query p ⦃ s => s.val = cowList p.query ⦄ := by
  unfold named_params.ParsedNamedParams.impl.query
  exact cow_deref_spec _ _

/-- `ParsedNamedParams::params`: the names, in order. -/
theorem named_params.ParsedNamedParams.impl.params_spec (p : named_params.ParsedNamedParams) :
    named_params.ParsedNamedParams.impl.params p ⦃ s => s.val = p.params.val ⦄ := by
  simp [named_params.ParsedNamedParams.impl.params, alloc.vec.Vec.deref]

end mysql_common
