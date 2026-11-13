import Defs.Convert

/-!
# SQL text: named placeholders, parameter lists and SQL literals

The definitions the specs of `named_params.rs`, `params.rs` and `Value::as_sql` are stated with.
All byte-level definitions are about ASCII: a byte `c` is the character with code `c.val`.

## 1. Placeholders in a query (`ParsedNamedParams::parse`)

The placeholder language, written from the crate's documentation and the MySQL lexical rules
(<https://dev.mysql.com/doc/refman/8.4/en/string-literals.html>, `.../comments.html`,
`.../identifiers.html>`), *not* from the crate's state machine. A query is cut into tokens
(`sqlLex`, maximal munch, left to right):

* `:name`, where `name` is `[a-z_][a-z0-9_]*` (as long as possible): a **named placeholder**;
* `?`: a **positional placeholder**;
* a **string literal** `'…'` or `"…"`: up to the first closing quote not preceded by a
  backslash escape (`\x` is two bytes of the literal). A doubled quote `''` inside a literal
  (MySQL's other escape) closes the literal and opens a new one, which gives the same
  placeholders;
* a **quoted identifier** `` `…` `` (no escapes; a doubled backtick likewise);
* a **comment**: `#…` to the end of the line, `--` followed by a space or control character
  (MySQL: whitespace or `iscntrl`, i.e. a byte `≤ 0x20` or `0x7F`) to the end of the line, or
  `/* … */` up to the first `*/`;
* the openers `/*!` (MySQL executable comment, whose body is SQL that the server runs) and
  `/*+` (optimizer hint): **not** comments; their bodies are scanned like any SQL text, so
  placeholders inside are recognised. (This is the crate's documented choice, its test
  `comments_with_question_marks`; for optimizer hints it is debatable, see `Specs/NamedParams`.)
  The closing `*/` of such a body is then ordinary text;
* any other byte: ordinary text.

Literals, identifiers and comments that are never closed extend to the end of the query.
Placeholders are not recognised inside literals, identifiers and comments.

`lex false` is this intended tokenizer (`sqlLex`). `lex true` (`crateLex`) is what the crate
actually does: the same, except at **the documented deviations**, each guarded by `crate` in
`lexAux` below — in each the crate's state machine moves on without re-examining a byte, so that
byte is taken as ordinary text:
1. the byte after a lone `/` (not starting a comment) or a lone `-` (not starting a comment);
2. the byte after `--` when it is not one of tab, form feed, CR, space (the crate does not
   treat `--` + newline, vertical tab or other control characters as a comment);
3. the byte after a named placeholder or after a lone `:`, unless it is `:`, `'` or `"`;
4. in a `/* */` comment, the byte after `/*`, and the byte after each `*` that does not close
   the comment, are skipped when looking for `*/` (so `/**/` and `/* x **/` are not closed).

`QuirkFree q` is a readable condition on the intended tokens under which none of these
deviations matters (`Specs/DefsSqlText.lean`: then `crateLex q = sqlLex q`).

## 2. Parameter maps (`Params`)

The map of `Params::Named` is the opaque model `Trusted.ParamsMap` of `FunsExternal.lean`; the
specs only use `Trusted.paramsMapLookup` (the value of a key) and the entries up to permutation,
never the iteration order. `intoValuesMissing` is the name `Params::into_values` reports.

## 3. SQL literals (`Value::as_sql`)

`quoteSql` is the MySQL C API's escaping (`mysql_real_escape_string_quote` with quote `'`:
backslash-escapes NUL, `\n`, `\r`, `\`, `'`, `"` and Ctrl-Z; in `NO_BACKSLASH_ESCAPES` mode only
doubles `'`). `sqlStrLit` is the server's reading of a `'`-quoted literal (the String Literals
page, table 11.1): `''` is `'`; outside `NO_BACKSLASH_ESCAPES`, `\` escapes the next byte
(`\0 \' \" \b \n \r \t \Z \\` as in the table, `\%` and `\_` keep their backslash, any other
`\x` is `x`); in `NO_BACKSLASH_ESCAPES` mode `\` is an ordinary byte. The reader is byte-wise,
which is right for the connection character sets in which the bytes `'` (0x27) and `\` (0x5C)
are always those characters (utf8mb4, utf8mb3, latin1, ascii, binary, …), and **not** for
`big5`, `cp932`, `gbk`, `gb18030`, `sjis`, whose multi-byte characters can end in 0x5C.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## 1. Placeholders -/

/-- A byte that can start a placeholder name: `a`–`z` or `_`. -/
def isNameStart (c : U8) : Bool := (97 ≤ c.val && c.val ≤ 122) || c.val == 95

/-- A byte that can continue a placeholder name: `a`–`z`, `0`–`9` or `_`. -/
def isNameChar (c : U8) : Bool := isNameStart c || (48 ≤ c.val && c.val ≤ 57)

/-- MySQL's condition on the byte after `--` for a comment: whitespace or a control character
    (`my_isspace || my_iscntrl`: `≤ 0x20` or `0x7F`). -/
def isSpaceOrCntrl (c : U8) : Bool := c.val ≤ 32 || c.val == 127

/-- The crate's condition on the byte after `--`: tab, form feed, CR or space (ASCII whitespace
    other than newline). -/
def isCrateDashSpace (c : U8) : Bool := c.val == 9 || c.val == 12 || c.val == 13 || c.val == 32

/-- A token of a query. -/
inductive Tok where
  /-- `:name` (the name without the colon). -/
  | named (nm : List U8)
  /-- `?`. -/
  | qmark
  /-- One byte of ordinary SQL text. -/
  | plain (c : U8)
  /-- A string literal, quoted identifier or comment (all its bytes): no placeholders inside. -/
  | skip (src : List U8)
deriving DecidableEq

/-- The bytes of the query a token stands for. -/
def Tok.src : Tok → List U8
  | .named n => byte 58 :: n
  | .qmark => [byte 63]
  | .plain c => [c]
  | .skip s => s

/-- The bytes a token becomes in the rewritten query: a named placeholder becomes `?`,
    everything else is copied. -/
def Tok.out : Tok → List U8
  | .named _ => [byte 63]
  | t => t.src

/-- The names of the named placeholders, in order (with repetitions). -/
def tokNames (ts : List Tok) : List (List U8) :=
  ts.filterMap fun | .named n => some n | _ => none

/-- Whether there is a positional placeholder. -/
def tokHasQmark (ts : List Tok) : Bool := ts.contains .qmark

/-- The prefix of `bs` up to and including the first byte satisfying `p` (all of `bs` if there
    is none), and the rest. -/
def upToIncl (p : U8 → Bool) : List U8 → List U8 × List U8
  | [] => ([], [])
  | c :: r => if p c then ([c], r) else ((c :: (upToIncl p r).1), (upToIncl p r).2)

/-- The rest of a string literal opened by the quote byte `q`, up to and including the closing
    quote: a backslash takes the next byte with it. Unclosed: all of it. -/
def strBody (q : Nat) : List U8 → List U8 × List U8
  | [] => ([], [])
  | c :: r =>
    if c.val = 92 then
      match r with
      | [] => ([c], [])
      | d :: r' => (c :: d :: (strBody q r').1, (strBody q r').2)
    else if c.val = q then ([c], r)
    else (c :: (strBody q r).1, (strBody q r).2)

/-- The rest of a `/* */` comment (after `/*`), up to and including the first `*/`. -/
def cBody : List U8 → List U8 × List U8
  | [] => ([], [])
  | c :: r =>
    if c.val = 42 then
      match r with
      | [] => ([c], [])
      | d :: r' => if d.val = 47 then ([c, d], r') else (c :: (cBody r).1, (cBody r).2)
    else (c :: (cBody r).1, (cBody r).2)

/-- Deviation 4: the crate's search for the end of a `/* */` comment, which skips the byte after
    each `*` that is not followed by `/`. -/
def cBodyCrate : List U8 → List U8 × List U8
  | [] => ([], [])
  | c :: r =>
    if c.val = 42 then
      match r with
      | [] => ([c], [])
      | d :: r' => if d.val = 47 then ([c, d], r') else (c :: d :: (cBodyCrate r').1, (cBodyCrate r').2)
    else (c :: (cBodyCrate r).1, (cBodyCrate r).2)

/-- The tokenizer, with fuel (each step consumes at least one byte, so `bs.length` suffices).
    `crate = false`: the intended language; `crate = true`: with the crate's deviations (each
    `if crate` branch below). -/
def lexAux (crate : Bool) : Nat → List U8 → List Tok
  | 0, bs => bs.map .plain
  | _ + 1, [] => []
  | n + 1, c :: r =>
    -- after a placeholder or a lone `:`: deviation 3
    let after (head : Tok) (rest : List U8) : List Tok :=
      match crate, rest with
      | true, d :: rest' =>
        if d.val = 58 ∨ d.val = 39 ∨ d.val = 34 then head :: lexAux crate n rest
        else head :: .plain d :: lexAux crate n rest'
      | _, _ => head :: lexAux crate n rest
    if c.val = 58 then                                         -- `:`
      match r with
      | d :: _ =>
        if isNameStart d then after (.named (r.takeWhile isNameChar)) (r.dropWhile isNameChar)
        else after (.plain c) r
      | [] => [.plain c]
    else if c.val = 63 then .qmark :: lexAux crate n r          -- `?`
    else if c.val = 39 ∨ c.val = 34 then                        -- `'`, `"`
      .skip (c :: (strBody c.val r).1) :: lexAux crate n (strBody c.val r).2
    else if c.val = 96 then                                     -- `` ` ``
      .skip (c :: (upToIncl (·.val = 96) r).1) :: lexAux crate n (upToIncl (·.val = 96) r).2
    else if c.val = 35 then                                     -- `#`
      .skip (c :: (upToIncl (·.val = 10) r).1) :: lexAux crate n (upToIncl (·.val = 10) r).2
    else if c.val = 47 then                                     -- `/`
      match r with
      | [] => [.plain c]
      | d :: r' =>
        if d.val = 42 then
          match r' with
          | [] => [.skip [c, d]]
          | e :: r'' =>
            if e.val = 33 ∨ e.val = 43 then .plain c :: .plain d :: .plain e :: lexAux crate n r''
            else if crate then
              .skip (c :: d :: e :: (cBodyCrate r'').1) :: lexAux crate n (cBodyCrate r'').2
            else .skip (c :: d :: (cBody r').1) :: lexAux crate n (cBody r').2
        else if crate then .plain c :: .plain d :: lexAux crate n r'      -- deviation 1
        else .plain c :: lexAux crate n r
    else if c.val = 45 then                                     -- `-`
      match r with
      | [] => [.plain c]
      | d :: r' =>
        if d.val = 45 then
          match r' with
          | [] => [.plain c, .plain d]
          | e :: r'' =>
            if (if crate then isCrateDashSpace e else isSpaceOrCntrl e) then
              .skip (c :: d :: (upToIncl (·.val = 10) r').1) ::
                lexAux crate n (upToIncl (·.val = 10) r').2
            else if crate then .plain c :: .plain d :: .plain e :: lexAux crate n r''  -- dev. 2
            else .plain c :: lexAux crate n r
        else if crate then .plain c :: .plain d :: lexAux crate n r'      -- deviation 1
        else .plain c :: lexAux crate n r
    else .plain c :: lexAux crate n r

/-- The tokens of a query (`crate = false`: intended; `true`: the crate's reading). -/
def lex (crate : Bool) (q : List U8) : List Tok := lexAux crate q.length q

/-- The intended tokens of a query. -/
abbrev sqlLex (q : List U8) : List Tok := lex false q

/-- The tokens as the crate reads them. -/
abbrev crateLex (q : List U8) : List Tok := lex true q

/-- A byte that can start a token other than ordinary text: `: / - # ' " ? `` ` ``. -/
def isSpecial (c : U8) : Bool :=
  c.val == 58 || c.val == 47 || c.val == 45 || c.val == 35 || c.val == 39 || c.val == 34 ||
  c.val == 63 || c.val == 96

/-- Whether token `u` may follow a lone `/` or `-` without deviation 1 mattering: an ordinary
    byte that starts nothing. -/
def Tok.harmlessAfterSlash : Tok → Bool
  | .plain c => !isSpecial c
  | _ => false

/-- Whether token `u` may follow a placeholder or lone `:` without deviation 3 mattering: it
    does not start with `/ - # ? `` ` ``. -/
def Tok.harmlessAfterColon : Tok → Bool
  | .qmark => false
  | t => match t.src with
    | c :: _ => !(c.val == 47 || c.val == 45 || c.val == 35 || c.val == 96)
    | [] => true

/-- A token on which deviations 2 and 4 matter: a `--` comment whose third byte is not tab,
    form feed, CR or space, or a `/* */` comment with an empty body or whose body ends in `*`
    (sufficient, not necessary: `/***/` is flagged although the crate closes it). -/
def Tok.isQuirkyComment : Tok → Bool
  | .skip s =>
    match s with
    | a :: b :: e :: _ =>
      (a.val == 45 && b.val == 45 && !isCrateDashSpace e) ||
      (a.val == 47 && b.val == 42 && 4 ≤ s.length &&
        (match s.reverse with
          | c1 :: c2 :: c3 :: _ => c1.val == 47 && c2.val == 42 && c3.val == 42
          | _ => false))
    | _ => false
  | _ => false

/-- No two adjacent tokens trigger a deviation. -/
def quirkFreeToks : List Tok → Bool
  | [] => true
  | [t] => !t.isQuirkyComment
  | t :: u :: ts =>
    !t.isQuirkyComment &&
    (match t with
      | .plain c =>
        if c.val = 47 ∨ c.val = 45 then u.harmlessAfterSlash
        else if c.val = 58 then u.harmlessAfterColon else true
      | .named _ => u.harmlessAfterColon
      | _ => true) &&
    quirkFreeToks (u :: ts)

/-- The query is read the same by the crate and by the intended tokenizer (see
    `Specs/DefsSqlText.lean`): no deviation applies to its intended tokens. -/
def QuirkFree (q : List U8) : Prop := quirkFreeToks (sqlLex q) = true

/-! ## 2. Parameter maps -/

/-- The name `Params::into_values` reports when a named parameter has no value (`names` is
    non-empty and some name has no value): the first such name, **unless every name after it is
    also missing, in which case the last name** (a quirk: it is missing too, but not the
    first). -/
noncomputable def intoValuesMissing (m : Trusted.ParamsMap) (names : List (List U8)) : List U8 :=
  let has (k : List U8) : Bool := (Trusted.paramsMapLookup m k).isSome
  match names.findIdx? (fun k => !has k) with
  | none => []
  | some j => if (names.drop (j + 1)).any has then names.getD j [] else names.getLastD []

/-! ## 3. SQL literals -/

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List U8 := utf8 s

/-- `mysql_real_escape_string_quote(…, '\'')` around quotes: the SQL string literal of `s`.
    `nbe` is the `NO_BACKSLASH_ESCAPES` SQL mode. -/
def quoteSql (nbe : Bool) (s : List U8) : List U8 :=
  let esc (c : U8) : List U8 :=
    if nbe then (if c.val = 39 then [c, c] else [c])
    else if c.val = 0 then [byte 92, byte 48]
    else if c.val = 10 then [byte 92, byte 110]
    else if c.val = 13 then [byte 92, byte 114]
    else if c.val = 26 then [byte 92, byte 90]
    else if c.val = 92 ∨ c.val = 39 ∨ c.val = 34 then [byte 92, c]
    else [c]
  byte 39 :: s.flatMap esc ++ [byte 39]

/-- What the server reads for the escape `\c` (MySQL String Literals, table 11.1). -/
def mysqlEscape (c : U8) : List U8 :=
  if c.val = 48 then [byte 0]
  else if c.val = 98 then [byte 8]
  else if c.val = 110 then [byte 10]
  else if c.val = 114 then [byte 13]
  else if c.val = 116 then [byte 9]
  else if c.val = 90 then [byte 26]
  else if c.val = 37 ∨ c.val = 95 then [byte 92, c]
  else [c]

/-- The server reading the inside of a `'`-quoted literal: the bytes it denotes and what follows
    the closing quote; `none` if the literal is not closed. -/
def sqlStrBody (nbe : Bool) : List U8 → Option (List U8 × List U8)
  | [] => none
  | c :: r =>
    if c.val = 39 then
      match r with
      | d :: r' =>
        if d.val = 39 then (sqlStrBody nbe r').map fun p => (c :: p.1, p.2) else some ([], r)
      | [] => some ([], [])
    else if c.val = 92 ∧ nbe = false then
      match r with
      | d :: r' => (sqlStrBody nbe r').map fun p => (mysqlEscape d ++ p.1, p.2)
      | [] => none
    else (sqlStrBody nbe r).map fun p => (c :: p.1, p.2)

/-- The server reading a `'`-quoted string literal at the front of `bs`. -/
def sqlStrLit (nbe : Bool) : List U8 → Option (List U8 × List U8)
  | c :: r => if c.val = 39 then sqlStrBody nbe r else none
  | [] => none

/-- An upper-case hexadecimal digit (`n < 16`). -/
def hexDigit (n : Nat) : U8 := if n < 10 then byte (48 + n) else byte (55 + n)

/-- A MySQL hexadecimal literal `0x…` of the bytes `bs`, two upper-case digits per byte. -/
def hexLit (bs : List U8) : List U8 :=
  ascii "0x" ++ bs.flatMap fun b => [hexDigit (b.val / 16), hexDigit (b.val % 16)]

/-- `n` in decimal, left-padded with `0` to at least `w` digits (never truncated). -/
def padDec (w n : Nat) : List U8 :=
  let ds := (Nat.toDigits 10 n).map fun c => byte c.toNat
  List.replicate (w - ds.length) (byte 48) ++ ds

/-- The SQL literal of a `DATE`/`DATETIME` value: `'YYYY-MM-DD'` if the time part is zero,
    else `'YYYY-MM-DD hh:mm:ss'`, with `.uuuuuu` if the microseconds are non-zero. Fields are
    not range-checked (e.g. month 13 is printed as `13`). -/
def dateSql (y mo d h mi s us : Nat) : List U8 :=
  let date := padDec 4 y ++ ascii "-" ++ padDec 2 mo ++ ascii "-" ++ padDec 2 d
  let time := ascii " " ++ padDec 2 h ++ ascii ":" ++ padDec 2 mi ++ ascii ":" ++ padDec 2 s
  ascii "'" ++ date ++
    (if h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0 then []
     else time ++ (if us = 0 then [] else ascii "." ++ padDec 6 us)) ++ ascii "'"

/-- The SQL literal of a `TIME` value: `'[-]hhh:mm:ss[.uuuuuu]'` with `hhh = 24·days + hours`
    (at least 3 digits) and the fraction only when the microseconds are non-zero. Not
    range-checked (MySQL's range is ±838:59:59). -/
def timeSql (neg : Bool) (d h mi s us : Nat) : List U8 :=
  ascii "'" ++ (if neg then ascii "-" else []) ++ padDec 3 (d * 24 + h) ++ ascii ":" ++
    padDec 2 mi ++ ascii ":" ++ padDec 2 s ++ (if us = 0 then [] else ascii "." ++ padDec 6 us) ++
    ascii "'"

end Defs

namespace Defs

/-- What `ParsedNamedParams::parse q` returns when the query's tokens are `ts`: an error exactly
    when there is a named and a positional placeholder; otherwise the query with each named
    placeholder replaced by `?` (the original slice, borrowed, when there are none) and the
    placeholder names in order. -/
def parsedAs (q : Slice U8) (ts : List Tok) :
    core.result.Result named_params.ParsedNamedParams named_params.MixedParamsError → Prop
  | .Err _ => tokNames ts ≠ [] ∧ tokHasQmark ts = true
  | .Ok p => ¬(tokNames ts ≠ [] ∧ tokHasQmark ts = true) ∧
      cowList p.query = ts.flatMap Tok.out ∧ p.params.val.map cowList = tokNames ts ∧
      (tokNames ts = [] → p.query = .Borrowed q)

end Defs
