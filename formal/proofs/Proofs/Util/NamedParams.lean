import Defs

/-! Helper lemmas for `Proofs/NamedParams/*` and `Proofs/Defs/LemmasSqlText.lean`: the tokenizer
`lex` (fuel independence, one-step unfolding) and the scanners it uses. -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Scanners: they split their input -/

theorem upToIncl_append (p : U8 → Bool) (r : List U8) : (upToIncl p r).1 ++ (upToIncl p r).2 = r := by
  induction r with
  | nil => rfl
  | cons c r ih => by_cases h : p c <;> simp [upToIncl, h, ih]

theorem strBody_append (q : Nat) : ∀ r : List U8, (strBody q r).1 ++ (strBody q r).2 = r
  | [] => rfl
  | c :: [] => by by_cases h : c.val = 92 <;> by_cases h' : c.val = q <;> simp [strBody, h, h']
  | c :: d :: r => by
    have ih1 := strBody_append q r
    have ih2 := strBody_append q (d :: r)
    by_cases h : c.val = 92 <;> by_cases h' : c.val = q <;> simp_all [strBody]

theorem cBody_append (r : List U8) : (cBody r).1 ++ (cBody r).2 = r := by
  induction r using cBody.induct <;> simp_all [cBody]

theorem cBodyCrate_append : ∀ r : List U8, (cBodyCrate r).1 ++ (cBodyCrate r).2 = r
  | [] => rfl
  | c :: [] => by by_cases h : c.val = 42 <;> simp [cBodyCrate, h]
  | c :: d :: r => by
    have ih1 := cBodyCrate_append r
    have ih2 := cBodyCrate_append (d :: r)
    by_cases h : c.val = 42 <;> by_cases h' : d.val = 47 <;> simp_all [cBodyCrate]

theorem upToIncl_len (p : U8 → Bool) (r : List U8) : (upToIncl p r).2.length ≤ r.length := by
  have := congrArg List.length (upToIncl_append p r); simp at this; omega

theorem strBody_len (q : Nat) (r : List U8) : (strBody q r).2.length ≤ r.length := by
  have := congrArg List.length (strBody_append q r); simp at this; omega

theorem cBody_len (r : List U8) : (cBody r).2.length ≤ r.length := by
  have := congrArg List.length (cBody_append r); simp at this; omega

theorem cBodyCrate_len (r : List U8) : (cBodyCrate r).2.length ≤ r.length := by
  have := congrArg List.length (cBodyCrate_append r); simp at this; omega


/-! ## One step of the tokenizer -/

/-- The body of `lexAux` on `c :: r`, with the recursive call `f`. -/
def lexStep (crate : Bool) (f : List U8 → List Tok) (c : U8) (r : List U8) : List Tok :=
    let after (head : Tok) (rest : List U8) : List Tok :=
      match crate, rest with
      | true, d :: rest' =>
        if d.val = 58 ∨ d.val = 39 ∨ d.val = 34 then head :: f rest
        else head :: .plain d :: f rest'
      | _, _ => head :: f rest
    if c.val = 58 then
      match r with
      | d :: _ =>
        if isNameStart d then after (.named (r.takeWhile isNameChar)) (r.dropWhile isNameChar)
        else after (.plain c) r
      | [] => [.plain c]
    else if c.val = 63 then .qmark :: f r
    else if c.val = 39 ∨ c.val = 34 then
      .skip (c :: (strBody c.val r).1) :: f (strBody c.val r).2
    else if c.val = 96 then
      .skip (c :: (upToIncl (·.val = 96) r).1) :: f (upToIncl (·.val = 96) r).2
    else if c.val = 35 then
      .skip (c :: (upToIncl (·.val = 10) r).1) :: f (upToIncl (·.val = 10) r).2
    else if c.val = 47 then
      match r with
      | [] => [.plain c]
      | d :: r' =>
        if d.val = 42 then
          match r' with
          | [] => [.skip [c, d]]
          | e :: r'' =>
            if e.val = 33 ∨ (e.val = 43 ∧ crate) then
              .plain c :: .plain d :: .plain e :: f r''
            else if crate then
              .skip (c :: d :: e :: (cBodyCrate r'').1) :: f (cBodyCrate r'').2
            else .skip (c :: d :: (cBody r').1) :: f (cBody r').2
        else if crate then .plain c :: .plain d :: f r'
        else .plain c :: f r
    else if c.val = 45 then
      match r with
      | [] => [.plain c]
      | d :: r' =>
        if d.val = 45 then
          match r' with
          | [] => [.plain c, .plain d]
          | e :: r'' =>
            if (if crate then isCrateDashSpace e else isSpaceOrCntrl e) then
              .skip (c :: d :: (upToIncl (·.val = 10) r').1) ::
                f (upToIncl (·.val = 10) r').2
            else if crate then .plain c :: .plain d :: .plain e :: f r''
            else .plain c :: f r
        else if crate then .plain c :: .plain d :: f r'
        else .plain c :: f r
    else .plain c :: f r

theorem lexAux_succ_cons (crate : Bool) (n : Nat) (c : U8) (r : List U8) :
    lexAux crate (n + 1) (c :: r) = lexStep crate (lexAux crate n) c r := rfl

theorem dropWhile_len {α : Type} (p : α → Bool) (r : List α) : (r.dropWhile p).length ≤ r.length :=
  List.Sublist.length_le (List.dropWhile_sublist p)

theorem lexStep_congr (crate : Bool) (f g : List U8 → List Tok) (c : U8) (r : List U8)
    (h : ∀ X : List U8, X.length ≤ r.length → f X = g X) :
    lexStep crate f c r = lexStep crate g c r := by
  have hs := strBody_len c.val r
  have hu1 := upToIncl_len (·.val = 96) r
  have hu2 := upToIncl_len (·.val = 10) r
  have hd := dropWhile_len isNameChar r
  have hr := h r le_rfl
  simp only [lexStep]
  by_cases h58 : c.val = 58
  · simp only [h58, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · rfl
    by_cases hn : isNameStart d
    · simp only [hn, ite_true]
      generalize List.dropWhile isNameChar (d :: r') = D at hd
      cases crate <;> rcases D with _ | ⟨x, D'⟩ <;> simp only [] <;> (try split_ifs) <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp at hd ⊢ <;> omega
    · simp only [hn, Bool.false_eq_true, ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp
  simp only [h58, ite_false]
  by_cases h63 : c.val = 63
  · simp [h63, hr]
  simp only [h63, ite_false]
  by_cases hq : c.val = 39 ∨ c.val = 34
  · simp [hq, h _ hs]
  simp only [hq, ite_false]
  by_cases h96 : c.val = 96
  · simp [h96, h _ hu1]
  simp only [h96, ite_false]
  by_cases h35 : c.val = 35
  · simp [h35, h _ hu2]
  simp only [h35, ite_false]
  by_cases h47 : c.val = 47
  · simp only [h47, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · rfl
    have hb := cBody_len r'
    by_cases h42 : d.val = 42
    · simp only [h42, ite_true]
      rcases r' with _ | ⟨e, r''⟩
      · rfl
      have hbc := cBodyCrate_len r''
      cases crate <;> (try simp only []) <;> split_ifs <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp at hb hbc ⊢ <;> try omega
    · simp only [h42, ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp
  simp only [h47, ite_false]
  by_cases h45 : c.val = 45
  · simp only [h45, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · rfl
    have hu3 := upToIncl_len (·.val = 10) r'
    by_cases h45' : d.val = 45
    · simp only [h45', ite_true]
      rcases r' with _ | ⟨e, r''⟩
      · rfl
      cases crate <;> (try simp only []) <;> split_ifs <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp at hu3 ⊢ <;> try omega
    · simp only [h45', ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;>
        (try simp only [List.cons.injEq, true_and]) <;> apply h <;> simp
  simp [h45, hr]

/-- Enough fuel gives the same tokens. -/
theorem lexAux_fuel (crate : Bool) : ∀ (n m : Nat) (bs : List U8),
    bs.length ≤ n → bs.length ≤ m → lexAux crate n bs = lexAux crate m bs
  | 0, m, bs, h, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; cases m <;> rfl
  | n + 1, 0, bs, _, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | n + 1, m + 1, [], _, _ => rfl
  | n + 1, m + 1, c :: r, h1, h2 => by
    rw [lexAux_succ_cons, lexAux_succ_cons]
    apply lexStep_congr
    intro X hX
    exact lexAux_fuel crate n m X (by simp at h1; omega) (by simp at h2; omega)

theorem lexAux_eq_lex (crate : Bool) (n : Nat) (bs : List U8) (h : bs.length ≤ n) :
    lexAux crate n bs = lex crate bs :=
  lexAux_fuel crate n bs.length bs h le_rfl

theorem lex_cons (crate : Bool) (c : U8) (r : List U8) :
    lex crate (c :: r) = lexStep crate (lex crate) c r := by
  unfold lex
  rw [List.length_cons, lexAux_succ_cons]
  apply lexStep_congr
  intro X hX
  exact lexAux_eq_lex crate _ X hX

theorem np_byte_self (x : U8) : byte x.val = x := by
  cases x; simp [byte, UScalar.val]

theorem np_byte_of_val (x : U8) (n : Nat) (h : x.val = n) : byte n = x := by
  rw [← h, np_byte_self]

theorem lexStep_src (crate : Bool) (f : List U8 → List Tok) (c : U8) (r : List U8)
    (hf : ∀ X, (f X).flatMap Tok.src = X) :
    (lexStep crate f c r).flatMap Tok.src = c :: r := by
  have hs := strBody_append c.val r
  have hu1 := upToIncl_append (·.val = 96) r
  have hu2 := upToIncl_append (·.val = 10) r
  simp only [lexStep]
  by_cases h58 : c.val = 58
  · simp only [h58, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · simp [Tok.src]
    have h58' := np_byte_of_val c 58 h58
    have htd := List.takeWhile_append_dropWhile (p := isNameChar) (l := d :: r')
    by_cases hn : isNameStart d
    · simp only [hn, ite_true]
      revert htd
      generalize List.dropWhile isNameChar (d :: r') = D
      generalize List.takeWhile isNameChar (d :: r') = T
      intro htd
      cases crate <;> rcases D with _ | ⟨x, D'⟩ <;> (try simp only []) <;> (try split_ifs) <;>
        simp_all [Tok.src]
    · simp only [hn, Bool.false_eq_true, ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;> simp_all [Tok.src]
  simp only [h58, ite_false]
  by_cases h63 : c.val = 63
  · simp [h63, hf, Tok.src, np_byte_of_val c 63 h63]
  simp only [h63, ite_false]
  by_cases hq : c.val = 39 ∨ c.val = 34
  · simp [hq, hf, Tok.src, hs]
  simp only [hq, ite_false]
  by_cases h96 : c.val = 96
  · simp [h96, hf, Tok.src, hu1]
  simp only [h96, ite_false]
  by_cases h35 : c.val = 35
  · simp [h35, hf, Tok.src, hu2]
  simp only [h35, ite_false]
  by_cases h47 : c.val = 47
  · simp only [h47, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · simp [Tok.src]
    have hb := cBody_append r'
    by_cases h42 : d.val = 42
    · simp only [h42, ite_true]
      rcases r' with _ | ⟨e, r''⟩
      · simp [Tok.src]
      have hbc := cBodyCrate_append r''
      cases crate <;> (try simp only []) <;> split_ifs <;> simp_all [Tok.src]
    · simp only [h42, ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;> simp_all [Tok.src]
  simp only [h47, ite_false]
  by_cases h45 : c.val = 45
  · simp only [h45, ite_true]
    rcases r with _ | ⟨d, r'⟩
    · simp [Tok.src]
    have hu3 := upToIncl_append (·.val = 10) r'
    by_cases h45' : d.val = 45
    · simp only [h45', ite_true]
      rcases r' with _ | ⟨e, r''⟩
      · simp [Tok.src]
      cases crate <;> (try simp only []) <;> split_ifs <;> simp_all [Tok.src]
    · simp only [h45', ite_false]
      cases crate <;> (try simp only []) <;> (try split_ifs) <;> simp_all [Tok.src]
  simp [h45, hf, Tok.src]

theorem lexAux_src (crate : Bool) : ∀ (n : Nat) (bs : List U8), (lexAux crate n bs).flatMap Tok.src = bs
  | 0, bs => by simp only [lexAux]; induction bs <;> simp_all [Tok.src]
  | _ + 1, [] => rfl
  | n + 1, c :: r => by
    rw [lexAux_succ_cons]; exact lexStep_src crate _ c r (lexAux_src crate n)

/-! ## The server's string-literal reader -/

theorem sqlStrBody_cons (nbe : Bool) (c : U8) (r : List U8) :
    sqlStrBody nbe (c :: r) =
    if c.val = 39 then
      match r with
      | d :: r' =>
        if d.val = 39 then (sqlStrBody nbe r').map fun p => (c :: p.1, p.2) else some ([], r)
      | [] => some ([], [])
    else if c.val = 92 ∧ nbe = false then
      match r with
      | d :: r' => (sqlStrBody nbe r').map fun p => (mysqlEscape d ++ p.1, p.2)
      | [] => none
    else (sqlStrBody nbe r).map fun p => (c :: p.1, p.2) := by
  rcases r with _ | ⟨d, r'⟩ <;> rfl

theorem np_byte_val (n : Nat) : (byte n).val = n % 256 := by
  show (BitVec.ofNat 8 n).toNat = n % 256
  simp

@[simp] theorem lex_nil (crate : Bool) : lex crate [] = [] := rfl


/-! ## A pure model of the crate's state machine (`parse_step`, the loop, the final fix-up) -/

open named_params (ParserState)

abbrev N3 := Nat × Nat × Nat

/-- The state after a byte that the crate re-examines (`rematch`). -/
def remat (c : U8) : ParserState :=
  if c.val = 58 then .MaybeInNamedParam else if c.val = 39 then .InStringLiteral 39#u8 false
  else if c.val = 34 then .InStringLiteral 34#u8 false else .TopLevel

/-- The state after a byte at top level. -/
def topNext (c : U8) : ParserState :=
  if c.val = 58 then .MaybeInNamedParam else if c.val = 47 then .MaybeInCComment1
  else if c.val = 45 then .MaybeInDoubleDashComment1 else if c.val = 35 then .InSharpComment
  else if c.val = 39 then .InStringLiteral 39#u8 false
  else if c.val = 34 then .InStringLiteral 34#u8 false
  else if c.val = 96 then .InQuotedIdentifier else .TopLevel

/-- `parse_step` on naturals. -/
def pstep (st : ParserState) (c : U8) (i : Nat) (hp : Bool) (cur : Nat) (ps : List N3) :
    ParserState × Bool × Nat × List N3 :=
  match st with
  | .TopLevel => (topNext c, hp || decide (c.val = 63), cur, ps)
  | .InStringLiteral s e =>
    ((if e then .InStringLiteral s false else if c = s then .TopLevel
      else .InStringLiteral s (decide (c.val = 92))), hp, cur, ps)
  | .MaybeInNamedParam =>
    if isNameStart c then (.InNamedParam, hp, cur, ps ++ [(i - 1, i, 0)]) else (remat c, hp, cur, ps)
  | .InNamedParam =>
    if isNameChar c then (.InNamedParam, hp, cur, ps)
    else (remat c, hp, cur + 1, ps.set cur ((ps[cur]!).1, (ps[cur]!).2.1, i))
  | .InSharpComment => (if c.val = 10 then .TopLevel else .InSharpComment, hp, cur, ps)
  | .MaybeInDoubleDashComment1 =>
    (if c.val = 45 then .MaybeInDoubleDashComment2 else .TopLevel, hp, cur, ps)
  | .MaybeInDoubleDashComment2 =>
    (if isCrateDashSpace c then .InDoubleDashComment else .TopLevel, hp, cur, ps)
  | .InDoubleDashComment => (if c.val = 10 then .TopLevel else .InDoubleDashComment, hp, cur, ps)
  | .MaybeInCComment1 => (if c.val = 42 then .MaybeInCComment2 else .TopLevel, hp, cur, ps)
  | .MaybeInCComment2 => (if c.val = 33 ∨ c.val = 43 then .TopLevel else .InCComment, hp, cur, ps)
  | .InCComment => (if c.val = 42 then .MaybeExitCComment else .InCComment, hp, cur, ps)
  | .MaybeExitCComment => (if c.val = 47 then .TopLevel else .InCComment, hp, cur, ps)
  | .InQuotedIdentifier => (if c.val = 96 then .TopLevel else .InQuotedIdentifier, hp, cur, ps)

/-- The loop, from position `i` on the remaining bytes. -/
def prun : ParserState → Bool → Nat → List N3 → Nat → List U8 → ParserState × Bool × Nat × List N3
  | st, hp, cur, ps, _, [] => (st, hp, cur, ps)
  | st, hp, cur, ps, i, c :: r =>
    let x := pstep st c i hp cur ps
    prun x.1 x.2.1 x.2.2.1 x.2.2.2 (i + 1) r

/-- The fix-up after the loop: close an open named parameter at the end of the query. -/
def pfin (st : ParserState) (cur : Nat) (ps : List N3) (len : Nat) : List N3 :=
  match st with
  | .InNamedParam => ps.set cur ((ps[cur]!).1, (ps[cur]!).2.1, len)
  | _ => ps

/-- What is left of the run: `have_positional` and the final triples. -/
def E (st : ParserState) (hp : Bool) (cur : Nat) (ps : List N3) (i : Nat) (r : List U8) :
    Bool × List N3 :=
  let R := prun st hp cur ps i r
  (R.2.1, pfin R.1 R.2.2.1 R.2.2.2 (i + r.length))

theorem E_nil (st : ParserState) (hp : Bool) (cur : Nat) (ps : List N3) (i : Nat) :
    E st hp cur ps i [] = (hp, pfin st cur ps i) := rfl

theorem E_cons (st : ParserState) (hp : Bool) (cur : Nat) (ps : List N3) (i : Nat) (c : U8)
    (r : List U8) : E st hp cur ps i (c :: r) =
      E (pstep st c i hp cur ps).1 (pstep st c i hp cur ps).2.1 (pstep st c i hp cur ps).2.2.1
        (pstep st c i hp cur ps).2.2.2 (i + 1) r := by
  simp only [E, prun, List.length_cons]; congr 2; omega

/-- The triples `(colon, start, end)` of the named placeholders, the tokens starting at `i`. -/
def trip : List Tok → Nat → List N3
  | [], _ => []
  | .named n :: ts, i => (i, i + 1, i + 1 + n.length) :: trip ts (i + 1 + n.length)
  | t :: ts, i => trip ts (i + t.src.length)

theorem trip_nonnamed (t : Tok) (ts : List Tok) (i : Nat) (h : ∀ n, t ≠ .named n) :
    trip (t :: ts) i = trip ts (i + t.src.length) := by
  cases t <;> simp_all [trip]

/-- A state that only waits for a byte satisfying `p`. -/
theorem E_until (S : ParserState) (p : U8 → Bool) (hS : S ≠ .InNamedParam)
    (hstep : ∀ c i hp cur ps, pstep S c i hp cur ps = (if p c then .TopLevel else S, hp, cur, ps))
    (hp : Bool) (cur : Nat) (ps : List N3) :
    ∀ (r : List U8) (i : Nat), E S hp cur ps i r =
      E .TopLevel hp cur ps (i + (upToIncl p r).1.length) (upToIncl p r).2
  | [], i => by cases S <;> simp_all [E_nil, upToIncl, pfin]
  | c :: r, i => by
    rw [E_cons, hstep]
    by_cases hc : p c
    · simp [hc, upToIncl]
    · simp only [hc, upToIncl, Bool.false_eq_true, ite_false, List.length_cons]
      rw [E_until S p hS hstep hp cur ps r (i + 1)]; congr 1; omega

theorem strBody_cons_ne (q : Nat) (c : U8) (r : List U8) (h1 : c.val ≠ 92) :
    strBody q (c :: r) = if c.val = q then ([c], r) else (c :: (strBody q r).1, (strBody q r).2) := by
  rcases r with _ | ⟨d, r'⟩ <;> simp [strBody, h1]

theorem E_str (sep : U8) (hsep : sep.val ≠ 92) (hp : Bool) (cur : Nat) (ps : List N3) :
    ∀ (r : List U8) (i : Nat), E (.InStringLiteral sep false) hp cur ps i r =
      E .TopLevel hp cur ps (i + (strBody sep.val r).1.length) (strBody sep.val r).2
  | [], i => by simp [E_nil, strBody, pfin]
  | c :: r, i => by
    rw [E_cons]
    have hcs : c = sep ↔ c.val = sep.val := ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
    by_cases h92 : c.val = 92
    · have hne : ¬ c = sep := fun h => hsep (h ▸ h92)
      rcases r with _ | ⟨d, r'⟩
      · simp [pstep, hne, h92, strBody, E_nil, pfin]
      · simp only [pstep, hne, h92, strBody, ite_false, ite_true, Bool.false_eq_true, decide_true,
          List.length_cons]
        rw [E_cons]; simp only [pstep, ite_true]
        rw [E_str sep hsep hp cur ps r' (i + 1 + 1)]; congr 1; omega
    · by_cases hc : c = sep
      · subst hc; simp [pstep, strBody_cons_ne _ _ _ h92]
      · have hc' : ¬ c.val = sep.val := fun h => hc (hcs.mpr h)
        simp only [pstep, hc, h92, hc', strBody_cons_ne _ _ _ h92, ite_false, Bool.false_eq_true,
          decide_false, List.length_cons]
        rw [E_str sep hsep hp cur ps r (i + 1)]; congr 1; omega

theorem cBodyCrate_cons_ne (c : U8) (r : List U8) (h1 : c.val ≠ 42) :
    cBodyCrate (c :: r) = (c :: (cBodyCrate r).1, (cBodyCrate r).2) := by
  rcases r with _ | ⟨d, r'⟩ <;> simp [cBodyCrate, h1]

theorem E_ccomment (hp : Bool) (cur : Nat) (ps : List N3) :
    ∀ (r : List U8) (i : Nat), E .InCComment hp cur ps i r =
      E .TopLevel hp cur ps (i + (cBodyCrate r).1.length) (cBodyCrate r).2
  | [], i => by simp [E_nil, cBodyCrate, pfin]
  | c :: r, i => by
    rw [E_cons]
    by_cases h42 : c.val = 42
    · rcases r with _ | ⟨d, r'⟩
      · simp [pstep, h42, cBodyCrate, E_nil, pfin]
      · rw [E_cons]
        by_cases h47 : d.val = 47
        · simp [pstep, h42, h47, cBodyCrate]
        · simp only [pstep, h42, h47, cBodyCrate, ite_false, ite_true, List.length_cons]
          rw [E_ccomment hp cur ps r' (i + 1 + 1)]; congr 1; omega
    · simp only [pstep, h42, cBodyCrate_cons_ne _ _ h42, ite_false, List.length_cons]
      rw [E_ccomment hp cur ps r (i + 1)]; congr 1; omega

theorem E_name (hp : Bool) (cur : Nat) (ps : List N3) :
    ∀ (T D : List U8) (i : Nat), (∀ x ∈ T, isNameChar x = true) →
      E .InNamedParam hp cur ps i (T ++ D) = E .InNamedParam hp cur ps (i + T.length) D
  | [], D, i, _ => by simp
  | c :: T, D, i, h => by
    rw [List.cons_append, E_cons]
    simp only [pstep, h c (by simp), ite_true, List.length_cons]
    rw [E_name hp cur ps T D (i + 1) (fun x hx => h x (by simp [hx]))]; congr 1; omega


theorem set_last (ps : List N3) (a b : N3) : (ps ++ [a]).set ps.length b = ps ++ [b] := by
  simp

theorem getElem!_last (ps : List N3) (a : N3) : (ps ++ [a])[ps.length]! = a := by
  simp

@[simp] theorem tokHasQmark_nil : tokHasQmark [] = false := rfl

@[simp] theorem tokHasQmark_cons (t : Tok) (ts : List Tok) :
    tokHasQmark (t :: ts) = (decide (t = .qmark) || tokHasQmark ts) := by
  simp [tokHasQmark, eq_comm]

@[simp] theorem trip_nil (i : Nat) : trip [] i = [] := rfl

@[simp] theorem trip_plain (c : U8) (ts : List Tok) (i : Nat) :
    trip (.plain c :: ts) i = trip ts (i + 1) := rfl

@[simp] theorem trip_qmark (ts : List Tok) (i : Nat) : trip (.qmark :: ts) i = trip ts (i + 1) := rfl

@[simp] theorem trip_skip (s : List U8) (ts : List Tok) (i : Nat) :
    trip (.skip s :: ts) i = trip ts (i + s.length) := rfl

@[simp] theorem trip_named (n : List U8) (ts : List Tok) (i : Nat) :
    trip (.named n :: ts) i = (i, i + 1, i + 1 + n.length) :: trip ts (i + 1 + n.length) := rfl

theorem remat_of_special (x : U8) (hx : x.val = 58 ∨ x.val = 39 ∨ x.val = 34) :
    remat x = topNext x ∧ x.val ≠ 63 := by
  rcases hx with hx | hx | hx <;> simp [remat, topNext, hx]

theorem remat_of_not_special (x : U8) (hx : ¬ (x.val = 58 ∨ x.val = 39 ∨ x.val = 34)) :
    remat x = .TopLevel := by
  simp only [not_or] at hx; simp [remat, hx.1, hx.2.1, hx.2.2]

/-- The top-level invariant, given for shorter inputs: after a token that the crate follows by
    the byte `x` without re-examining it unless it is `:`, `'` or `"`. -/
theorem E_after (n : Nat)
    (IH : ∀ X : List U8, X.length ≤ n → ∀ (hp : Bool) (ps : List N3) (i : Nat),
      E .TopLevel hp ps.length ps i X = (hp || tokHasQmark (lex true X), ps ++ trip (lex true X) i))
    (x : U8) (D : List U8) (hlen : (x :: D).length ≤ n) (hp : Bool) (ps : List N3) (j : Nat) :
    E (remat x) hp ps.length ps (j + 1) D =
      let A := if x.val = 58 ∨ x.val = 39 ∨ x.val = 34 then lex true (x :: D)
        else .plain x :: lex true D
      (hp || tokHasQmark A, ps ++ trip A j) := by
  by_cases hx : x.val = 58 ∨ x.val = 39 ∨ x.val = 34
  · obtain ⟨h1, h2⟩ := remat_of_special x hx
    have : E .TopLevel hp ps.length ps j (x :: D) = E (topNext x) hp ps.length ps (j + 1) D := by
      rw [E_cons]; simp [pstep, h2]
    rw [h1, ← this, IH _ hlen]; simp [hx]
  · rw [remat_of_not_special x hx, IH D (by simp at hlen; omega)]
    simp [hx]


theorem mem_takeWhile_p {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α), x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases ha : p a
    · rw [List.takeWhile_cons_of_pos ha] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · exact mem_takeWhile_p p l x h
    · rw [List.takeWhile_cons_of_neg ha] at h; simp at h

theorem isNameChar_of_start (d : U8) (h : isNameStart d = true) : isNameChar d = true := by
  simp [isNameChar, h]

/-- **The loop invariant**: from top level, the run reads the crate's tokens of the rest. -/
theorem E_top : ∀ (n : Nat) (r : List U8), r.length ≤ n → ∀ (hp : Bool) (ps : List N3) (i : Nat),
    E .TopLevel hp ps.length ps i r = (hp || tokHasQmark (lex true r), ps ++ trip (lex true r) i)
  | 0, r, h, hp, ps, i => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; simp [E_nil, pfin]
  | _ + 1, [], _, hp, ps, i => by simp [E_nil, pfin]
  | n + 1, c :: r, hlen, hp, ps, i => by
    have IH := E_top n
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
    rw [E_cons, lex_cons]
    simp only [pstep, lexStep]
    by_cases h58 : c.val = 58
    · simp only [h58, topNext, ite_true, show (58 : Nat) ≠ 63 by decide, decide_false,
        Bool.or_false]
      rcases r with _ | ⟨d, r'⟩
      · simp [E_nil, pfin]
      simp only [List.length_cons] at hlen
      rw [E_cons]
      by_cases hn : isNameStart d
      · simp only [pstep, hn, ite_true, Nat.add_sub_cancel]
        have htd := List.takeWhile_append_dropWhile (p := isNameChar) (l := r')
        have hT : ∀ x ∈ r'.takeWhile isNameChar, isNameChar x = true :=
          fun x hx => mem_takeWhile_p _ _ _ hx
        have hD : (r'.dropWhile isNameChar).length ≤ r'.length := dropWhile_len _ _
        have hDh : ∀ x D', r'.dropWhile isNameChar = x :: D' → isNameChar x = false := by
          intro x D' h
          have := List.head_dropWhile_not isNameChar (l := r') (by simp [h])
          simpa [h] using this
        rw [List.takeWhile_cons_of_pos (isNameChar_of_start d hn),
          List.dropWhile_cons_of_pos (isNameChar_of_start d hn)]
        conv_lhs => rw [← htd]
        rw [E_name _ _ _ _ _ _ hT]
        revert hD hDh
        generalize r'.takeWhile isNameChar = T
        generalize r'.dropWhile isNameChar = D
        intro hD hDh
        rcases D with _ | ⟨x, D'⟩
        · simp only [E_nil, pfin, getElem!_last, set_last]
          simp only [tokHasQmark_cons, tokHasQmark_nil, lex_nil, trip_named, trip_nil]
          simp; omega
        · rw [E_cons]
          simp only [pstep, hDh x D' rfl, Bool.false_eq_true, ite_false, getElem!_last, set_last]
          have := E_after n IH x D' (by simp at hD ⊢; omega) hp (ps ++ [(i, i + 1, i + 1 + 1 + T.length)])
            (i + 1 + 1 + T.length)
          simp only [List.length_append, List.length_singleton] at this
          rw [this]
          simp only [List.append_assoc, List.singleton_append]
          split_ifs <;> simp [show i + 1 + (T.length + 1) = i + 1 + 1 + T.length by omega]
      · simp only [pstep, hn, Bool.false_eq_true, ite_false]
        have := E_after n IH d r' hlen hp ps (i + 1)
        rw [this]
        split_ifs <;> simp
    simp only [h58, ite_false]
    by_cases h63 : c.val = 63
    · simp [h63, topNext, IH r hlen]
    simp only [h63, ite_false, decide_false, Bool.or_false]
    by_cases hq : c.val = 39 ∨ c.val = 34
    · have hs := strBody_len 39 r; have hs2 := strBody_len 34 r
      rcases hq with hq | hq
      · simp only [topNext, hq, ite_true, ite_false, true_or, show (39 : Nat) ≠ 58 by decide,
          show (39 : Nat) ≠ 47 by decide, show (39 : Nat) ≠ 45 by decide,
          show (39 : Nat) ≠ 35 by decide]
        rw [E_str _ (by decide), show (39#u8 : U8).val = 39 from rfl, IH (strBody 39 r).2 (by omega)]
        simp; first | omega | (congr 1; omega)
      · simp only [topNext, hq, ite_true, ite_false, or_true, show (34 : Nat) ≠ 58 by decide,
          show (34 : Nat) ≠ 47 by decide, show (34 : Nat) ≠ 45 by decide,
          show (34 : Nat) ≠ 35 by decide, show (34 : Nat) ≠ 39 by decide]
        rw [E_str _ (by decide), show (34#u8 : U8).val = 34 from rfl, IH (strBody 34 r).2 (by omega)]
        simp; first | omega | (congr 1; omega)
    simp only [hq, ite_false]
    simp only [not_or] at hq
    by_cases h96 : c.val = 96
    · have hs := upToIncl_len (·.val = 96) r
      simp only [topNext, h96, ite_true, ite_false, show (96 : Nat) ≠ 58 by decide,
        show (96 : Nat) ≠ 47 by decide, show (96 : Nat) ≠ 45 by decide,
        show (96 : Nat) ≠ 35 by decide, show (96 : Nat) ≠ 39 by decide,
        show (96 : Nat) ≠ 34 by decide]
      rw [E_until .InQuotedIdentifier (·.val = 96) (by simp) (by intros; simp [pstep]),
        IH (upToIncl (·.val = 96) r).2 (by omega)]
      simp; first | omega | (congr 1; omega)
    simp only [h96, ite_false]
    by_cases h35 : c.val = 35
    · have hs := upToIncl_len (·.val = 10) r
      simp only [topNext, h35, ite_true, ite_false, show (35 : Nat) ≠ 58 by decide,
        show (35 : Nat) ≠ 47 by decide, show (35 : Nat) ≠ 45 by decide]
      rw [E_until .InSharpComment (·.val = 10) (by simp) (by intros; simp [pstep]),
        IH (upToIncl (·.val = 10) r).2 (by omega)]
      simp; first | omega | (congr 1; omega)
    simp only [h35, ite_false]
    by_cases h47 : c.val = 47
    · simp only [topNext, h47, ite_true, ite_false, show (47 : Nat) ≠ 58 by decide]
      rcases r with _ | ⟨d, r'⟩
      · simp [E_nil, pfin]
      simp only [List.length_cons] at hlen
      rw [E_cons]
      by_cases h42 : d.val = 42
      · simp only [pstep, h42, ite_true]
        rcases r' with _ | ⟨e, r''⟩
        · simp [E_nil, pfin]
        simp only [List.length_cons] at hlen
        rw [E_cons]
        by_cases he : e.val = 33 ∨ e.val = 43
        · simp only [pstep, he, ite_true, and_true]
          rw [IH r'' (by omega)]
          simp
        · simp only [pstep, he, ite_false, and_true]
          have hs := cBodyCrate_len r''
          rw [E_ccomment, IH (cBodyCrate r'').2 (by omega)]
          simp; first | omega | (congr 1; omega)
      · simp only [pstep, h42, ite_false]
        rw [IH r' (by omega)]
        simp
    simp only [h47, ite_false]
    by_cases h45 : c.val = 45
    · simp only [topNext, h45, ite_true, ite_false, show (45 : Nat) ≠ 58 by decide,
        show (45 : Nat) ≠ 47 by decide]
      rcases r with _ | ⟨d, r'⟩
      · simp [E_nil, pfin]
      simp only [List.length_cons] at hlen
      rw [E_cons]
      by_cases h45' : d.val = 45
      · simp only [pstep, h45', ite_true]
        rcases r' with _ | ⟨e, r''⟩
        · simp [E_nil, pfin]
        simp only [List.length_cons] at hlen
        rw [E_cons]
        by_cases he : isCrateDashSpace e
        · have he10 : ¬ e.val = 10 := by
            simp only [isCrateDashSpace, Bool.or_eq_true, beq_iff_eq] at he; omega
          have hs := upToIncl_len (·.val = 10) r''
          simp only [pstep, he, ite_true, upToIncl, he10, decide_false, Bool.false_eq_true,
            ite_false]
          rw [E_until .InDoubleDashComment (·.val = 10) (by simp) (by intros; simp [pstep]),
            IH (upToIncl (·.val = 10) r'').2 (by omega)]
          simp; first | omega | (congr 1; omega)
        · simp only [pstep, he, ite_false, Bool.false_eq_true]
          rw [IH r'' (by omega)]
          simp
      · simp only [pstep, h45', ite_false]
        rw [IH r' (by omega)]
        simp
    simp only [h45, ite_false]
    simp only [topNext, h58, h47, h45, h35, hq.1, hq.2, h96, ite_false]
    rw [IH r hlen]
    simp

/-! ## `parse_step` refines `pstep` -/

open Result

/-- The parameter triples as naturals. -/
def toN (v : List (Usize × Usize × Usize)) : List N3 := v.map fun t => (t.1.val, t.2.1.val, t.2.2.val)

@[simp] theorem u8_mk_val (b : BitVec 8) : (UScalar.mk b : U8).val = b.toNat := rfl

theorem parse_step_spec (st : ParserState) (c : U8) (i : Usize) (hp : Bool) (cur : Usize)
    (params : alloc.vec.Vec (Usize × Usize × Usize))
    (h1 : st = .InNamedParam → cur.val < params.length)
    (h2 : st = .MaybeInNamedParam → 1 ≤ i.val)
    (h3 : params.length < Usize.max) (h4 : cur.val < Usize.max) :
    named_params.parse_step st c i hp cur params ⦃ r =>
      (r.1, r.2.1, r.2.2.1.val, toN r.2.2.2.val) = pstep st c i.val hp cur.val (toN params.val) ⦄ := by
  unfold named_params.parse_step
  cases st
  case TopLevel => simp only [pstep]; split <;> simp_all [topNext]
  case InStringLiteral s e =>
    simp only [pstep]
    cases e <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · by_cases hc : c = s
      · simp [hc]
      · by_cases h92 : c = 92#u8
        · subst h92; simp [hc]
        · have : ¬ c.val = 92 := fun h => h92 (UScalar.eq_of_val_eq h)
          simp [hc, h92, this]
    · simp
  case MaybeInNamedParam =>
    have hi := h2 rfl
    simp only [pstep, toN]
    have hv : ∀ x y : U8, x ≤ y ↔ x.val ≤ y.val := fun _ _ => Iff.rfl
    by_cases ha : 97#u8 ≤ c <;> by_cases hb : c ≤ 122#u8 <;> simp only [ha, hb, ite_true, ite_false]
    · have hn : isNameStart c = true := by simp [hv] at ha hb; simp [isNameStart]; omega
      simp only [hn, ite_true]
      step as ⟨i1, hi1⟩
      step as ⟨p2, hp2⟩
      simp_all
    all_goals split
    all_goals first
      | (exfalso; revert ha; decide)
      | (rename_i _ hne
         have hc95 : c.val ≠ 95 := fun h => hne (UScalar.eq_of_val_eq (by simpa using h))
         have hn : isNameStart c = false := by
           simp only [hv] at ha hb; simp [isNameStart, hc95]; simp at ha hb; omega
         simp only [hn, Bool.false_eq_true, ite_false]
         split <;> simp_all [remat])
      | (have hn95 : isNameStart (95#8#uscalar) = true := by decide
         have hi' : (1#usize : Usize).val ≤ i.val := by simpa using hi
         simp only [hn95, ite_true]
         step as ⟨i1, hi1⟩; step as ⟨p2, hp2⟩; simp_all)
  case InNamedParam =>
    have hcur := h1 rfl
    simp only [pstep, toN]
    have hv : ∀ x y : U8, x ≤ y ↔ x.val ≤ y.val := fun _ _ => Iff.rfl
    by_cases ha : 97#u8 ≤ c <;> by_cases hb : c ≤ 122#u8 <;> by_cases hc : 48#u8 ≤ c <;>
      by_cases hd : c ≤ 57#u8 <;> simp only [ha, hb, hc, hd, ite_true, ite_false]
    all_goals try (exfalso; simp only [hv] at ha hb hc hd; simp at ha hb hc hd; omega)
    all_goals try (
      have hn : isNameChar c = true := by
        simp only [hv] at ha hb hc hd; simp [isNameChar, isNameStart]; simp at ha hb hc hd; omega
      simp [hn])
    all_goals split
    all_goals first
      | (have hn : isNameChar (95#8#uscalar) = true := by decide
         simp [hn]; done)
      | (rename_i _ hne
         have hc95 : c.val ≠ 95 := fun h => hne (UScalar.eq_of_val_eq (by simpa using h))
         have hn : isNameChar c = false := by
           simp only [hv] at ha hb hc hd; simp [isNameChar, isNameStart, hc95]; simp at ha hb hc hd; omega
         simp only [hn, Bool.false_eq_true, ite_false, Std.bind_ok,
           alloc.vec.Vec.index_mut_slice_index]
         have hcur' : cur.val + 1 ≤ Usize.max := by omega
         step as ⟨x, hx1, hx2⟩
         obtain ⟨⟨a1, a2, a3⟩, back⟩ := x
         simp only at hx1 hx2 ⊢
         subst hx2
         step as ⟨cur2, hcur2⟩
         have hget : (List.map (fun t : Usize × Usize × Usize => (t.1.val, t.2.1.val, t.2.2.val))
             params.val)[cur.val]! = (a1.val, a2.val, a3.val) := by
           rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
             List.getElem?_eq_getElem (by simpa using hcur), ← hx1]; rfl
         rw [hget]
         clear hget hx1 hv ha hb hc hd h1 h2 hn
         split <;> (try split) <;> simp_all [remat, List.map_set])
  all_goals simp only [pstep]
  all_goals (split <;> (try split_ifs) <;> simp_all [isCrateDashSpace])


/-! ## The loop -/

/-- The bounds kept by the loop. -/
def pInv (st : ParserState) (cur len i : Nat) : Prop :=
  (st = .InNamedParam → cur < len) ∧ (st = .MaybeInNamedParam → 1 ≤ i) ∧ len ≤ i ∧ cur ≤ len

theorem remat_ne (c : U8) : remat c ≠ .InNamedParam ∧ remat c ≠ .MaybeInNamedParam ∨ remat c = .MaybeInNamedParam := by
  unfold remat; split_ifs <;> simp

theorem topNext_ne (c : U8) : topNext c ≠ .InNamedParam := by
  unfold topNext; split_ifs <;> simp

theorem pInv_step (st : ParserState) (c : U8) (i : Nat) (hp : Bool) (cur : Nat) (ps : List N3)
    (h : pInv st cur ps.length i) :
    pInv (pstep st c i hp cur ps).1 (pstep st c i hp cur ps).2.2.1
      (pstep st c i hp cur ps).2.2.2.length (i + 1) := by
  have hr := remat_ne c
  have ht := topNext_ne c
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold pInv
  cases st <;> simp only [pstep] <;> (try split_ifs) <;> simp_all <;> (try omega) <;>
    (rcases hr with hr | hr <;> simp_all <;> omega)

theorem pInv_run : ∀ (r : List U8) (st : ParserState) (hp : Bool) (cur : Nat) (ps : List N3) (i : Nat),
    pInv st cur ps.length i →
    pInv (prun st hp cur ps i r).1 (prun st hp cur ps i r).2.2.1 (prun st hp cur ps i r).2.2.2.length
      (i + r.length)
  | [], _, _, _, _, _, h => h
  | c :: r, st, hp, cur, ps, i, h => by
    simp only [prun, List.length_cons]
    have := pInv_run r _ (pstep st c i hp cur ps).2.1 _ _ (i + 1) (pInv_step st c i hp cur ps h)
    rwa [show i + 1 + r.length = i + (r.length + 1) by omega] at this

theorem parse_loop_unfold (q : Slice U8) (st : ParserState) (hp : Bool) (cur : Usize)
    (params : alloc.vec.Vec (Usize × Usize × Usize)) (i : Usize) :
    named_params.ParsedNamedParams.parse_loop q st hp cur params i =
      (do
        let r ← named_params.ParsedNamedParams.parse_loop.body q st hp cur params i
        match r with
        | .cont (a, b, c, d, e) => named_params.ParsedNamedParams.parse_loop q a b c d e
        | .done x => ok x) := by
  conv_lhs => unfold named_params.ParsedNamedParams.parse_loop; rw [loop]
  congr 1
  funext r
  rcases r with ⟨a, b, c, d, e⟩ | x <;> rfl

theorem parse_loop_spec (q : Slice U8) : ∀ (r : List U8) (st : ParserState) (hp : Bool) (cur : Usize)
    (params : alloc.vec.Vec (Usize × Usize × Usize)) (i : Usize),
    q.val.drop i.val = r → i.val ≤ q.length → pInv st cur.val params.length i.val →
    named_params.ParsedNamedParams.parse_loop q st hp cur params i ⦃ R =>
      (R.1, R.2.1, R.2.2.1.val, toN R.2.2.2.val) = prun st hp cur.val (toN params.val) i.val r ∧
      pInv R.1 R.2.2.1.val R.2.2.2.length q.length ⦄
  | [], st, hp, cur, params, i, hr, hle, hinv => by
    have hi : q.length ≤ i.val := by simpa [Slice.length] using hr
    rw [parse_loop_unfold]
    unfold named_params.ParsedNamedParams.parse_loop.body
    have hlt : ¬ (i < q.len) := by scalar_tac
    simp only [hlt, ↓reduceIte, Std.bind_ok, WP.spec_ok, prun]
    refine ⟨trivial, ?_⟩
    rw [show q.length = i.val by omega]; exact hinv
  | c :: r, st, hp, cur, params, i, hr, hle, hinv => by
    have hi : i.val < q.length := by
      have : (q.val.drop i.val).length = r.length + 1 := by rw [hr]; rfl
      simp [Slice.length] at this ⊢; omega
    have hc : q.val[i.val]! = c := by
      rw [List.getElem!_eq_getElem?_getD, ← List.head?_drop, hr]; rfl
    rw [parse_loop_unfold]
    unfold named_params.ParsedNamedParams.parse_loop.body
    have hlt : i < q.len := by scalar_tac
    obtain ⟨h1, h2, h3, h4⟩ := hinv
    simp only [hlt, ↓reduceIte]
    step as ⟨c', hc'⟩
    step with parse_step_spec as ⟨x, hx⟩
    obtain ⟨st', hp', cur', ps'⟩ := x
    have hcc : c' = c := by rw [← hc, hc']; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Slice.length] using hi)]
    subst hcc
    have hlenN : (toN params.val).length = params.length := by simp [toN]
    have hinv' := pInv_step st c' i.val hp cur.val (toN params.val) (by rw [hlenN]; exact ⟨h1, h2, h3, h4⟩)
    simp only at hx
    rw [← hx] at hinv'
    simp only [toN, List.length_map] at hinv'
    step as ⟨i3, hi3⟩
    trace_state
    have hdrop : q.val.drop i3.val = r := by
      rw [hi3, ← List.drop_drop, hr]; rfl
    apply WP.spec_mono (parse_loop_spec q r st' hp' cur' ps' i3 hdrop (by rw [hi3]; omega)
      (by rw [hi3]; exact hinv'))
    intro R hR
    obtain ⟨hR1, hR2⟩ := hR
    refine ⟨?_, hR2⟩
    rw [hR1, prun, ← hx, hi3]


/-! ## `substitute_params` -/

theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ v' => v'.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intro x _; rfl))
  intro l hl
  simp [hl.1]

@[simp] theorem tokNames_nil : tokNames [] = [] := rfl

theorem tokNames_cons_named (n : List U8) (ts : List Tok) :
    tokNames (.named n :: ts) = n :: tokNames ts := rfl

theorem tokNames_cons_other (t : Tok) (ts : List Tok) (h : ∀ n, t ≠ .named n) :
    tokNames (t :: ts) = tokNames ts := by
  cases t <;> simp_all [tokNames]

theorem trip_length : ∀ (ts : List Tok) (i : Nat), (trip ts i).length = (tokNames ts).length
  | [], _ => rfl
  | .named n :: ts, i => by simp [trip_length ts, tokNames_cons_named]
  | .qmark :: ts, i => by simp [trip_length ts, tokNames_cons_other]
  | .plain c :: ts, i => by simp [trip_length ts, tokNames_cons_other]
  | .skip s :: ts, i => by simp [trip_length ts, tokNames_cons_other]

theorem substitute_spec (q : Slice U8) (P : Slice (Usize × Usize × Usize)) :
    ∀ (ts : List Tok) (X : List U8) (k last : Usize) (rq : alloc.vec.Vec U8)
      (op : alloc.vec.Vec (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))),
    q.val = X ++ ts.flatMap Tok.src → toN (P.val.drop k.val) = trip ts X.length →
    last.val ≤ X.length → rq.length ≤ last.val → op.length = k.val →
    named_params.substitute_params q P k last rq op ⦃ R =>
      R.1.val = rq.val ++ X.drop last.val ++ ts.flatMap Tok.out ∧
      R.2.val.map cowList = op.val.map cowList ++ tokNames ts ⦄
  | [], X, k, last, rq, op, hq, hP, hl, hrq, hop => by
    simp only [List.flatMap_nil, List.append_nil] at hq
    have hk : P.length ≤ k.val := by
      have := congrArg List.length hP; simp [toN, trip] at this; simp [Slice.length]; omega
    rw [named_params.substitute_params]
    have hlt : ¬ (k < P.len) := by scalar_tac
    simp only [hlt, ↓reduceIte, Slice.index_SliceIndexRangeFromUsizeSliceInst]
    have hql : q.length ≤ Usize.max := by scalar_tac
    step as ⟨s, hs1, hs2⟩
    step with extend_u8_spec as ⟨v, hv⟩
    simp [hv, hs1, hq]
  | t :: ts, X, k, last, rq, op, hq, hP, hl, hrq, hop => by
    by_cases hn : ∃ n, t = .named n
    · obtain ⟨n, rfl⟩ := hn
      rw [trip_named] at hP
      have hkl : k.val < P.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by simp [Slice.length] at hc ⊢; omega)] at hP
        simp [toN] at hP
      have hkl' : k.val < P.val.length := by simpa [Slice.length] using hkl
      obtain ⟨a, b, e, hPk⟩ : ∃ a b e, P.val[k.val]'hkl' = (a, b, e) := ⟨_, _, _, rfl⟩
      have hdrop : P.val.drop k.val = (a, b, e) :: P.val.drop (k.val + 1) := by
        rw [← hPk]; simp
      rw [hdrop] at hP
      simp only [toN, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hP
      obtain ⟨⟨ha, hb, he⟩, hP'⟩ := hP
      have hql : q.length ≤ Usize.max := by scalar_tac
      have hqlen : q.length = X.length + 1 + n.length + (ts.flatMap Tok.src).length := by
        simp [Slice.length, hq, Tok.src]; omega
      rw [named_params.substitute_params]
      have hlt : k < P.len := by scalar_tac
      simp only [hlt, ↓reduceIte]
      step as ⟨t0, ht0⟩
      rw [ht0, hPk]
      have hPl : P.length ≤ Usize.max := by scalar_tac
      step as ⟨s1, hs1, hs1l⟩
      step with extend_u8_spec as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨s2, hs2, hs2l⟩
      step as ⟨o1, ho1⟩
      step as ⟨k1, hk1⟩
      have hX : q.val = (X ++ byte 58 :: n) ++ ts.flatMap Tok.src := by simp [hq, Tok.src]
      have hs1v : s1.val = X.drop last.val := by
        rw [hs1, hq, ha, List.slice, List.drop_append_of_le_length hl,
          List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
      have hs2v : s2.val = n := by
        rw [hs2, hX, hb, he]; simp [List.slice, List.drop_append]
      have hXl : (X ++ byte 58 :: n).length = X.length + 1 + n.length := by simp; omega
      apply WP.spec_mono (substitute_spec q P ts (X ++ byte 58 :: n) k1 e v2 o1 hX
        (by rw [hk1, hXl]; simpa [toN] using hP') (by rw [hXl, he])
        (by
          show v2.val.length ≤ e.val
          have e1 : s1.val.length = a.val - last.val := hs1l
          have e2 : rq.val.length ≤ last.val := hrq
          rw [hv2, hv1]; simp only [List.length_append, List.length_singleton]; omega)
        (by simp [ho1, hop, hk1]))
      intro R hR
      obtain ⟨hR1, hR2⟩ := hR
      refine ⟨?_, ?_⟩
      · rw [hR1, hv2, hv1, hs1v, he]
        have hd0 : List.drop (X.length + 1 + n.length) (X ++ byte 58 :: n) = [] :=
          List.drop_eq_nil_of_le (by rw [hXl])
        rw [hd0]
        have h63 : (63#u8 : U8) = byte 63 := by decide
        simp [Tok.out, h63]
      · rw [hR2, ho1, tokNames_cons_named]; simp [cowList, hs2v]
    · have hn' : ∀ n, t ≠ .named n := fun n h => hn ⟨n, h⟩
      rw [trip_nonnamed _ _ _ hn'] at hP
      have hout : t.out = t.src := by cases t <;> simp_all [Tok.out]
      apply WP.spec_mono (substitute_spec q P ts (X ++ t.src) k last rq op
        (by simp [hq]) (by simpa using hP) (by simp; omega) hrq hop)
      intro R hR
      obtain ⟨hR1, hR2⟩ := hR
      refine ⟨?_, ?_⟩
      · rw [hR1, List.drop_append_of_le_length hl]; simp [hout]
      · rw [hR2, tokNames_cons_other _ _ hn']


/-! ## When the crate's reading is the intended one -/

/-- `L` ends with `**/`. -/
def ess (L : List U8) : Bool :=
  match L.reverse with
  | c1 :: c2 :: c3 :: _ => c1.val == 47 && c2.val == 42 && c3.val == 42
  | _ => false

theorem ess_cons (c : U8) (L : List U8) (h : ess L = true) : ess (c :: L) = true := by
  unfold ess at *
  rw [List.reverse_cons]
  split at h
  · rename_i c1 c2 c3 rest heq; rw [heq]; simpa using h
  · simp at h

theorem ess_three (a b c : U8) : ess [a, b, c] = (c.val == 47 && b.val == 42 && a.val == 42) := rfl

theorem cBody_cons_ne (c : U8) (r : List U8) (h1 : c.val ≠ 42) :
    cBody (c :: r) = (c :: (cBody r).1, (cBody r).2) := by
  rcases r with _ | ⟨d, r'⟩ <;> simp [cBody, h1]

/-- Deviation 4 does not matter unless the comment ends with `**/` (or is `/**/`). -/
theorem cBody_crate : ∀ (n : Nat) (X : List U8), X.length ≤ n →
    (ess (cBody X).1 = false → cBodyCrate X = cBody X) ∧
    (∀ d : U8, ess (cBody (d :: X)).1 = false → (cBody (d :: X)).1 ≠ [byte 42, byte 47] →
      (d :: (cBodyCrate X).1, (cBodyCrate X).2) = cBody (d :: X))
  | 0, X, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    refine ⟨fun _ => rfl, fun d _ _ => ?_⟩
    by_cases hd : d.val = 42 <;> simp [cBody, cBodyCrate, hd]
  | n + 1, X, hX => by
    have IH := cBody_crate n
    have hS : ess (cBody X).1 = false → cBodyCrate X = cBody X := by
      intro he
      rcases X with _ | ⟨c, r⟩
      · rfl
      by_cases hc : c.val = 42
      · rcases r with _ | ⟨d, r'⟩
        · simp [cBody, cBodyCrate, hc]
        by_cases hd : d.val = 47
        · simp [cBody, cBodyCrate, hc, hd]
        · have hT := (IH r' (by simp at hX; omega)).2 d
          have e1 : cBody (c :: d :: r') = (c :: (cBody (d :: r')).1, (cBody (d :: r')).2) := by
            simp [cBody, hc, hd]
          have e2 : cBodyCrate (c :: d :: r') =
              (c :: d :: (cBodyCrate r').1, (cBodyCrate r').2) := by
            simp [cBodyCrate, hc, hd]
          rw [e1] at he ⊢; rw [e2]
          simp only at he
          have h1 : ess (cBody (d :: r')).1 = false := by
            cases h : ess (cBody (d :: r')).1
            · rfl
            · rw [ess_cons c _ h] at he; exact absurd he (by simp)
          have h2 : (cBody (d :: r')).1 ≠ [byte 42, byte 47] := by
            intro h; rw [h] at he
            rw [ess_three] at he; simp [np_byte_val, hc] at he
          rw [← hT h1 h2]
      · rw [cBody_cons_ne _ _ hc] at he ⊢; rw [cBodyCrate_cons_ne _ _ hc]
        simp only at he
        have h1 : ess (cBody r).1 = false := by
          cases h : ess (cBody r).1
          · rfl
          · rw [ess_cons c _ h] at he; exact absurd he (by simp)
        rw [(IH r (by simp at hX; omega)).1 h1]
    refine ⟨hS, fun d he hne => ?_⟩
    by_cases hd : d.val = 42
    · rcases X with _ | ⟨f, X'⟩
      · simp [cBody, cBodyCrate, hd]
      by_cases hf : f.val = 47
      · exfalso; apply hne
        simp [cBody, hd, hf, np_byte_of_val d 42 hd, np_byte_of_val f 47 hf]
      · have e1 : cBody (d :: f :: X') = (d :: (cBody (f :: X')).1, (cBody (f :: X')).2) := by
          simp [cBody, hd, hf]
        rw [e1] at he ⊢
        simp only at he
        have h1 : ess (cBody (f :: X')).1 = false := by
          cases h : ess (cBody (f :: X')).1
          · rfl
          · rw [ess_cons d _ h] at he; exact absurd he (by simp)
        rw [hS h1]
    · rw [cBody_cons_ne _ _ hd] at he ⊢
      simp only at he
      have h1 : ess (cBody X).1 = false := by
        cases h : ess (cBody X).1
        · rfl
        · rw [ess_cons d _ h] at he; exact absurd he (by simp)
      rw [hS h1]


theorem qf_tail (t : Tok) (ts : List Tok) (h : quirkFreeToks (t :: ts) = true) :
    quirkFreeToks ts = true := by
  rcases ts with _ | ⟨u, ts⟩
  · rfl
  · simp only [quirkFreeToks, Bool.and_eq_true] at h; exact h.2

theorem qf_head (t : Tok) (ts : List Tok) (h : quirkFreeToks (t :: ts) = true) :
    t.isQuirkyComment = false := by
  rcases ts with _ | ⟨u, ts⟩
  · simpa [quirkFreeToks] using h
  · simp only [quirkFreeToks, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.1

theorem qf_named (n : List U8) (u : Tok) (ts : List Tok)
    (h : quirkFreeToks (.named n :: u :: ts) = true) : u.harmlessAfterColon = true := by
  simp only [quirkFreeToks, Bool.and_eq_true] at h; exact h.1.2

theorem qf_plain (c : U8) (u : Tok) (ts : List Tok)
    (h : quirkFreeToks (.plain c :: u :: ts) = true) :
    (c.val = 47 ∨ c.val = 45 → u.harmlessAfterSlash = true) ∧
    (c.val = 58 → u.harmlessAfterColon = true) := by
  simp only [quirkFreeToks, Bool.and_eq_true] at h
  have h2 := h.1.2
  constructor
  · intro hc; simpa [hc] using h2
  · intro hc; simpa [hc] using h2

theorem lex_plain_of_not_special (crate : Bool) (x : U8) (r : List U8) (hx : isSpecial x = false) :
    lex crate (x :: r) = .plain x :: lex crate r := by
  simp only [isSpecial, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨h58, h47⟩, h45⟩, h35⟩, h39⟩, h34⟩, h63⟩, h96⟩ := hx
  rw [lex_cons]; simp [lexStep, h58, h47, h45, h35, h39, h34, h63, h96]

/-- The first intended token of `d :: r`. -/
theorem lex_false_head (d : U8) (r : List U8) :
    lex false (d :: r) = .plain d :: lex false r ∨
    (d.val = 58 ∧ ∃ n ts, lex false (d :: r) = .named n :: ts) ∨
    (d.val = 63 ∧ lex false (d :: r) = .qmark :: lex false r) ∨
    (∃ s ts, lex false (d :: r) = .skip (d :: s) :: ts ∧
      (d.val = 39 ∨ d.val = 34 ∨ d.val = 96 ∨ d.val = 35 ∨ d.val = 47 ∨ d.val = 45)) := by
  rw [lex_cons]
  simp only [lexStep]
  by_cases h58 : d.val = 58
  · simp only [h58, ite_true]
    rcases r with _ | ⟨e, r'⟩
    · left; simp
    · by_cases hn : isNameStart e
      · right; left; simp [hn]
      · left; simp [hn]
  simp only [h58, ite_false]
  by_cases h63 : d.val = 63
  · simp [h63]
  simp only [h63, ite_false]
  by_cases hq : d.val = 39 ∨ d.val = 34
  · simp only [hq, ite_true]; right; right; right
    exact ⟨_, _, rfl, by rcases hq with h | h <;> simp [h]⟩
  simp only [hq, ite_false]
  by_cases h96 : d.val = 96
  · simp only [h96, ite_true]; right; right; right; exact ⟨_, _, rfl, by simp_all⟩
  simp only [h96, ite_false]
  by_cases h35 : d.val = 35
  · simp only [h35, ite_true]; right; right; right; exact ⟨_, _, rfl, by simp_all⟩
  simp only [h35, ite_false]
  by_cases h47 : d.val = 47
  · simp only [h47, ite_true]
    rcases r with _ | ⟨e, r'⟩
    · left; simp
    by_cases h42 : e.val = 42
    · simp only [h42, ite_true]
      rcases r' with _ | ⟨f, r''⟩
      · right; right; right; exact ⟨_, _, rfl, by simp_all⟩
      by_cases h33 : f.val = 33
      · left
        simp only [h33, true_or, ite_true]
        rw [lex_plain_of_not_special false e _ (by simp [isSpecial, h42]),
          lex_plain_of_not_special false f _ (by simp [isSpecial, h33])]
      · simp only [h33, Bool.false_eq_true, and_false, or_self, ite_false]
        right; right; right; exact ⟨_, _, rfl, by simp_all⟩
    · simp only [h42, ite_false, Bool.false_eq_true]; left; simp
  simp only [h47, ite_false]
  by_cases h45 : d.val = 45
  · simp only [h45, ite_true]
    rcases r with _ | ⟨e, r'⟩
    · left; simp
    by_cases h45' : e.val = 45
    · simp only [h45', ite_true]
      rcases r' with _ | ⟨f, r''⟩
      · left; rw [lex_cons]; simp [lexStep, h45']
      by_cases hf : isSpaceOrCntrl f
      · simp only [hf, Bool.false_eq_true, ite_true, ite_false]
        right; right; right; exact ⟨_, _, rfl, by simp_all⟩
      · simp only [hf, Bool.false_eq_true, ite_false]; left; simp
    · simp only [h45', ite_false, Bool.false_eq_true]; left; simp
  simp only [h45, ite_false]
  left; simp


theorem after_eq (n : Nat)
    (IH : ∀ X : List U8, X.length ≤ n → quirkFreeToks (lex false X) = true → lex true X = lex false X)
    (head : Tok) (x : U8) (D : List U8) (hlen : (x :: D).length ≤ n)
    (hq : quirkFreeToks (head :: lex false (x :: D)) = true)
    (hh : ∀ u ts, lex false (x :: D) = u :: ts → u.harmlessAfterColon = true) :
    (if x.val = 58 ∨ x.val = 39 ∨ x.val = 34 then head :: lex true (x :: D)
      else head :: .plain x :: lex true D) = head :: lex false (x :: D) := by
  have hq' := qf_tail _ _ hq
  split_ifs with hx
  · rw [IH _ hlen hq']
  · rcases lex_false_head x D with h | ⟨h58, _⟩ | ⟨_, h⟩ | ⟨s, ts, h, hs⟩
    · rw [h] at hq' ⊢
      rw [IH D (by simp at hlen; omega) (qf_tail _ _ hq')]
    · exact absurd (Or.inl h58) hx
    · have := hh _ _ h; simp [Tok.harmlessAfterColon] at this
    · have := hh _ _ h
      simp only [Tok.harmlessAfterColon, Bool.not_eq_true', Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] at this
      omega

theorem slash_eq (n : Nat)
    (IH : ∀ X : List U8, X.length ≤ n → quirkFreeToks (lex false X) = true → lex true X = lex false X)
    (c d : U8) (r : List U8) (hc : c.val = 47 ∨ c.val = 45) (hlen : r.length ≤ n)
    (hq : quirkFreeToks (.plain c :: lex false (d :: r)) = true) :
    Tok.plain c :: Tok.plain d :: lex true r = .plain c :: lex false (d :: r) := by
  rcases lex_false_head d r with h | ⟨_, nm, ts, h⟩ | ⟨_, h⟩ | ⟨s, ts, h, _⟩
  · rw [h] at hq ⊢
    rw [IH r hlen (qf_tail _ _ (qf_tail _ _ hq))]
  all_goals (rw [h] at hq; have := (qf_plain _ _ _ hq).1 hc; simp [Tok.harmlessAfterSlash] at this)

theorem cBody_fst_cons (e : U8) (r : List U8) : ∃ L, (cBody (e :: r)).1 = e :: L := by
  rcases r with _ | ⟨d, r'⟩
  · by_cases he : e.val = 42 <;> simp [cBody, he]
  · by_cases he : e.val = 42
    · by_cases hd : d.val = 47 <;> simp [cBody, he, hd]
    · simp [cBody_cons_ne _ _ he]

theorem quirky_of_ess (c d : U8) (L : List U8) (hc : c.val = 47) (hd : d.val = 42)
    (h : ess L = true) : (Tok.skip (c :: d :: L)).isQuirkyComment = true := by
  unfold ess at h
  split at h
  · rename_i c1 c2 c3 rest heq
    have hL : L = (c1 :: c2 :: c3 :: rest).reverse := by rw [← heq, List.reverse_reverse]
    subst hL
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases hr : rest.reverse with _ | ⟨x, xs⟩ <;>
      simp [Tok.isQuirkyComment, hc, hd, hr, h1, h2, h3, List.reverse_cons]
  · simp at h

theorem lex_crate_eq : ∀ (n : Nat) (q : List U8), q.length ≤ n →
    quirkFreeToks (lex false q) = true → lex true q = lex false q
  | 0, q, h, _ => by rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, c :: r, hlen, hq => by
    have IH := lex_crate_eq n
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
    rw [lex_cons false] at hq
    rw [lex_cons true, lex_cons false]
    simp only [lexStep] at hq ⊢
    by_cases h58 : c.val = 58
    · simp only [h58, ite_true] at hq ⊢
      rcases r with _ | ⟨d, r'⟩
      · rfl
      simp only [List.length_cons] at hlen
      by_cases hn : isNameStart d
      · simp only [hn, ite_true] at hq ⊢
        have hD := dropWhile_len isNameChar (d :: r')
        revert hq hD
        generalize List.dropWhile isNameChar (d :: r') = D
        intro hq hD
        rcases D with _ | ⟨x, D'⟩
        · rfl
        · exact after_eq n IH _ x D' (by simp at hD ⊢; omega) hq
            (fun u ts h => by rw [h] at hq; exact qf_named _ _ _ hq)
      · simp only [hn, Bool.false_eq_true, ite_false] at hq ⊢
        exact after_eq n IH _ d r' (by simp; omega) hq
          (fun u ts h => by rw [h] at hq; exact (qf_plain _ _ _ hq).2 h58)
    simp only [h58, ite_false] at hq ⊢
    by_cases h63 : c.val = 63
    · simp only [h63, ite_true] at hq ⊢
      rw [IH r hlen (qf_tail _ _ hq)]
    simp only [h63, ite_false] at hq ⊢
    by_cases hqt : c.val = 39 ∨ c.val = 34
    · simp only [hqt, ite_true] at hq ⊢
      rw [IH _ (le_trans (strBody_len _ _) hlen) (qf_tail _ _ hq)]
    simp only [hqt, ite_false] at hq ⊢
    by_cases h96 : c.val = 96
    · simp only [h96, ite_true] at hq ⊢
      rw [IH _ (le_trans (upToIncl_len _ _) hlen) (qf_tail _ _ hq)]
    simp only [h96, ite_false] at hq ⊢
    by_cases h35 : c.val = 35
    · simp only [h35, ite_true] at hq ⊢
      rw [IH _ (le_trans (upToIncl_len _ _) hlen) (qf_tail _ _ hq)]
    simp only [h35, ite_false] at hq ⊢
    by_cases h47 : c.val = 47
    · simp only [h47, ite_true] at hq ⊢
      rcases r with _ | ⟨d, r'⟩
      · rfl
      simp only [List.length_cons] at hlen
      by_cases h42 : d.val = 42
      · simp only [h42, ite_true] at hq ⊢
        rcases r' with _ | ⟨e, r''⟩
        · rfl
        simp only [List.length_cons] at hlen
        by_cases h33 : e.val = 33
        · simp only [h33, true_or, ite_true] at hq ⊢
          rw [IH r'' (by omega) (qf_tail _ _ (qf_tail _ _ (qf_tail _ _ hq)))]
        by_cases h43 : e.val = 43
        · exfalso
          simp only [h43, and_false, ite_false,
            Bool.false_eq_true] at hq
          have := qf_head _ _ hq
          obtain ⟨L, hL⟩ := cBody_fst_cons e r''
          rw [hL] at this
          simp [Tok.isQuirkyComment, h47, h42, h43] at this
        · simp only [h33, h43, false_or, and_false, and_true, ite_false,
            Bool.false_eq_true] at hq ⊢
          have hQ := qf_head _ _ hq
          have hess : ess (cBody (e :: r'')).1 = false := by
            cases h : ess (cBody (e :: r'')).1
            · rfl
            · rw [quirky_of_ess c d _ h47 h42 h] at hQ; exact absurd hQ (by simp)
          have hne : (cBody (e :: r'')).1 ≠ [byte 42, byte 47] := by
            intro h; rw [h] at hQ
            simp [Tok.isQuirkyComment, h47, h42, np_byte_val] at hQ
          have hT := (cBody_crate r''.length r'' le_rfl).2 e hess hne
          rw [← hT] at hq ⊢
          simp only at hq ⊢
          rw [IH _ (by have := cBodyCrate_len r''; omega) (qf_tail _ _ hq)]
      · simp only [h42, ite_false] at hq ⊢
        exact slash_eq n IH c d r' (Or.inl h47) (by omega) hq
    simp only [h47, ite_false] at hq ⊢
    by_cases h45 : c.val = 45
    · simp only [h45, ite_true] at hq ⊢
      rcases r with _ | ⟨d, r'⟩
      · rfl
      simp only [List.length_cons] at hlen
      by_cases h45' : d.val = 45
      · simp only [h45', ite_true] at hq ⊢
        rcases r' with _ | ⟨e, r''⟩
        · rfl
        simp only [List.length_cons] at hlen
        by_cases hc : isCrateDashSpace e
        · have hs : isSpaceOrCntrl e = true := by
            simp only [isCrateDashSpace, Bool.or_eq_true, beq_iff_eq] at hc
            simp only [isSpaceOrCntrl, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
          simp only [hc, hs, Bool.false_eq_true, ↓reduceIte] at hq ⊢
          rw [IH _ (le_trans (upToIncl_len _ _) (by simp; omega)) (qf_tail _ _ hq)]
        by_cases hs : isSpaceOrCntrl e
        · exfalso
          simp only [hc, hs, ite_true, Bool.false_eq_true, ite_false] at hq
          have := qf_head _ _ hq
          have hU : ∃ L, (upToIncl (fun x : U8 => decide (x.val = 10)) (e :: r'')).1 = e :: L := by
            by_cases he : e.val = 10 <;> simp [upToIncl, he]
          obtain ⟨L, hL⟩ := hU
          rw [hL] at this
          simp [Tok.isQuirkyComment, h45, h45', hc] at this
        · exfalso
          simp only [hc, hs, Bool.false_eq_true, ite_false] at hq
          rcases lex_false_head d (e :: r'') with h | ⟨_, nm, ts, h⟩ | ⟨_, h⟩ | ⟨s, ts, h, _⟩
          all_goals (rw [h] at hq; have := (qf_plain _ _ _ hq).1 (Or.inr h45))
          · simp [Tok.harmlessAfterSlash, isSpecial, h45'] at this
          all_goals simp [Tok.harmlessAfterSlash] at this
      · simp only [h45', ite_false] at hq ⊢
        exact slash_eq n IH c d r' (Or.inr h45) (by omega) hq
    simp only [h45, ite_false] at hq ⊢
    rw [IH r hlen (qf_tail _ _ hq)]

end Defs
