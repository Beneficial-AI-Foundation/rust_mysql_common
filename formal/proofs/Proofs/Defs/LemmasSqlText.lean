import Defs
import Proofs.Util.NamedParams

/-! Facts about the SQL-text definitions (`formal/specs/Defs/SqlText.lean`) (spec file:
`Specs/DefsSqlText.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- Tokenizing loses nothing: the tokens' bytes are the query (in both readings). -/
theorem lex_src (crate : Bool) (q : List U8) : (lex crate q).flatMap Tok.src = q := by
  exact lexAux_src crate _ q

/-- On a `QuirkFree` query the crate's reading is the intended one. -/
theorem crateLex_eq_sqlLex (q : List U8) (h : QuirkFree q) : crateLex q = sqlLex q := by
  exact lex_crate_eq q.length q le_rfl h

/-- An example of the intended language: placeholders in a quoted identifier, string literals
    (with `\"` and `''` escapes) and comments are not placeholders, and the query is
    `QuirkFree`. -/
theorem sqlLex_example :
    let q := ascii "SELECT :a, `x:y`, \"q\\\":z\" FROM t /* :c */ WHERE x = 'it''s :c' AND y = :b -- :d\n# :e"
    QuirkFree q ∧ tokNames (sqlLex q) = [ascii "a", ascii "b"] := by
  intro q; unfold QuirkFree; decide

/-- The server reads `quoteSql nbe s` back as `s` (any bytes `s`), and the literal ends exactly
    at its last byte unless the following text starts with `'`. -/
theorem sqlStrLit_quoteSql (nbe : Bool) (s rest : List U8)
    (hr : rest.head?.map (·.val) ≠ some 39) :
    sqlStrLit nbe (quoteSql nbe s ++ rest) = some (s, rest) := by
  have h39 : (byte 39).val = 39 := by simp [np_byte_val]
  simp only [quoteSql, sqlStrLit, List.cons_append, List.append_assoc, h39, ↓reduceIte]
  have hnil : sqlStrBody nbe (byte 39 :: rest) = some ([], rest) := by
    rw [sqlStrBody_cons]; simp only [h39, ↓reduceIte]
    rcases rest with _ | ⟨d, r⟩
    · rfl
    · have hd : ¬ d.val = 39 := by simpa using hr
      simp [hd]
  cases nbe <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · induction s with
    | nil => simpa using hnil
    | cons c s ih =>
      simp only [List.nil_append] at ih; rw [List.flatMap_cons, List.append_assoc]
      by_cases h0 : c.val = 0
      · simp [h0, sqlStrBody_cons, ih, mysqlEscape, np_byte_val, np_byte_of_val c 0 h0]
      by_cases h10 : c.val = 10
      · simp [h10, sqlStrBody_cons, ih, mysqlEscape, np_byte_val, np_byte_of_val c 10 h10]
      by_cases h13 : c.val = 13
      · simp [h13, sqlStrBody_cons, ih, mysqlEscape, np_byte_val, np_byte_of_val c 13 h13]
      by_cases h26 : c.val = 26
      · simp [h26, sqlStrBody_cons, ih, mysqlEscape, np_byte_val, np_byte_of_val c 26 h26]
      by_cases hq : c.val = 92 ∨ c.val = 39 ∨ c.val = 34
      · rcases hq with hq | hq | hq <;> simp [hq, sqlStrBody_cons, ih, mysqlEscape, np_byte_val]
      · simp only [not_or] at hq
        simp [h0, h10, h13, h26, hq, sqlStrBody_cons, ih]
  · induction s with
    | nil => simpa using hnil
    | cons c s ih =>
      simp only [List.nil_append] at ih; rw [List.flatMap_cons, List.append_assoc]
      by_cases hq : c.val = 39
      · simp [hq, sqlStrBody_cons, ih]
      · simp [hq, sqlStrBody_cons, ih]

/-- **Mode mismatch** (security): `no_backslash_escape` must be the server's
    `NO_BACKSLASH_ESCAPES` mode. Quoted for one mode and read in the other, a value can end the
    literal early and inject SQL, in both directions. -/
theorem sqlStrLit_mode_mismatch :
    sqlStrLit true (quoteSql false (ascii "x' OR 1=1 -- ")) =
      some (ascii "x\\", ascii " OR 1=1 -- '") ∧
    sqlStrLit false (quoteSql true (ascii "x\\' OR 1=1 -- ")) =
      some (ascii "x'", ascii " OR 1=1 -- '") := by
  decide

/-- A hexadecimal literal contains only `0`, `x` and upper-case hex digits. -/
theorem hexLit_chars (bs : List U8) :
    ∀ c ∈ hexLit bs, c ∈ ascii "0x0123456789ABCDEF" := by
  have hd : ∀ n < 16, hexDigit n ∈ ascii "0x0123456789ABCDEF" := by decide
  intro c hc
  simp only [hexLit, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with hc | ⟨b, _, hc | hc⟩
  · exact (by decide : ∀ c ∈ ascii "0x", c ∈ ascii "0x0123456789ABCDEF") c hc
  · subst hc; exact hd _ (by have : b.val < 256 := b.bv.isLt; omega)
  · subst hc; exact hd _ (Nat.mod_lt _ (by decide))

/-- The name `into_values` reports is one of the names, and has no value. -/
theorem intoValuesMissing_spec (m : Trusted.ParamsMap) (names : List (List U8))
    (h : ∃ n ∈ names, Trusted.paramsMapLookup m n = none) :
    intoValuesMissing m names ∈ names ∧
      Trusted.paramsMapLookup m (intoValuesMissing m names) = none := by
  simp only [intoValuesMissing]
  rcases hf : names.findIdx? (fun k => !(Trusted.paramsMapLookup m k).isSome) with _ | j
  · exfalso
    rw [List.findIdx?_eq_none_iff] at hf
    obtain ⟨n, hn, hl⟩ := h
    have := hf n hn
    simp [hl] at this
  · obtain ⟨hj, hpj, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hpj
    simp only []
    split_ifs with hany
    · rw [List.getD_eq_getElem _ _ hj]
      exact ⟨List.getElem_mem hj, hpj⟩
    · 
      simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true,
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hany
      have hne : names ≠ [] := List.ne_nil_of_length_pos (by omega)
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
      refine ⟨List.getLast_mem hne, ?_⟩
      rw [List.getLast_eq_getElem]
      by_cases hk : names.length - 1 = j
      · simp only [hk]; exact hpj
      · apply hany
        rw [List.mem_iff_getElem]
        refine ⟨names.length - 1 - (j + 1), by simp; omega, ?_⟩
        rw [List.getElem_drop]; congr 1; omega

end Defs
