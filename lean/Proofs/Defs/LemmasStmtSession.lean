import Defs
import Proofs.Defs.Lemmas
import Proofs.Util.ParseBuf

/-! Sanity lemmas about `Defs/CmdPackets.lean`, `Defs/SessionState.lean`, `Defs/BinlogCmd.lean`
(recalled in `Specs/DefsStmtSession.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace Defs

/-- `COM_STMT_PREPARE_OK` round trip: the reader reads the protocol layout back (fields in
    range). -/
theorem stmtOkRead_stmtOkEnc (s : StmtOk)
    (hs : s.stmtId < 2 ^ 32 ∧ s.numColumns < 2 ^ 16 ∧ s.numParams < 2 ^ 16 ∧ s.warnings < 2 ^ 16)
    (tail : List U8) :
    stmtOkRead (stmtOkEnc s ++ tail) = (some s, tail) := by
  obtain ⟨a, b, c, d⟩ := s
  obtain ⟨ha, hb, hc, hd⟩ := hs
  have ea := PBUtil.leNat_leBytes 4 a
  have eb := PBUtil.leNat_leBytes 2 b
  have ec := PBUtil.leNat_leBytes 2 c
  have ed := PBUtil.leNat_leBytes 2 d
  have la := PBUtil.length_leBytes 4 a
  have lb := PBUtil.length_leBytes 2 b
  have lc := PBUtil.length_leBytes 2 c
  have ld := PBUtil.length_leBytes 2 d
  simp only at ha hb hc hd
  rw [Nat.mod_eq_of_lt ha] at ea
  rw [Nat.mod_eq_of_lt hb] at eb
  rw [Nat.mod_eq_of_lt hc] at ec
  rw [Nat.mod_eq_of_lt hd] at ed
  unfold stmtOkEnc
  generalize leBytes 4 a = La at *
  generalize leBytes 2 b = Lb at *
  generalize leBytes 2 c = Lc at *
  generalize leBytes 2 d = Ld at *
  match La, Lb, Lc, Ld, la, lb, lc, ld with
  | [a0, a1, a2, a3], [b0, b1], [c0, c1], [d0, d1], _, _, _, _ =>
    simp [stmtOkRead, byte, ea, eb, ec, ed]
    split
    · omega
    · rfl

private theorem ssInfoRead_ssInfoEnc (i : SsInfo) (t : List U8) (h : i.2.length < 2 ^ 64) :
    ssInfoRead (ssInfoEnc i ++ t) = (some i, t) := by
  obtain ⟨ty, d⟩ := i
  have hty : sessionStateTypeOfCode (byte (sessionStateTypeCode ty)).val = some ty := by
    cases ty <;> rfl
  simp only [ssInfoEnc, List.cons_append, ssInfoRead, hty, checkedLenencStr_lenencStr _ _ h]

private theorem ssInfosFuel_ssInfoEnc (is : List SsInfo) (h : ∀ i ∈ is, i.2.length < 2 ^ 64)
    (n : Nat) (hn : (is.flatMap ssInfoEnc).length ≤ n) :
    ssInfosFuel n (is.flatMap ssInfoEnc) = some is := by
  induction is generalizing n with
  | nil => simp [ssInfosFuel]
  | cons i is ih =>
    have hne : ssInfoEnc i ≠ [] := by simp [ssInfoEnc]
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.flatMap_cons, List.length_append, hb, List.length_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hr := ssInfoRead_ssInfoEnc i (is.flatMap ssInfoEnc) (h i (by simp))
    rw [List.flatMap_cons, hb, List.cons_append]
    rw [hb, List.cons_append] at hr
    simp only [ssInfosFuel, hr]
    rw [ih (fun j hj => h j (by simp [hj])) m (by omega)]
    rfl

/-- Session state round trip: a sequence of entries in the protocol layout is read back. -/
theorem ssInfos_ssInfoEnc (is : List SsInfo) (h : ∀ i ∈ is, i.2.length < 2 ^ 64) :
    ssInfos (is.flatMap ssInfoEnc) = some is :=
  ssInfosFuel_ssInfoEnc is h _ le_rfl

/-- **Crate bug** (bulk types read from 3 bytes): a one-parameter request with its type, as the
    crate itself serializes it (`bulkReqEnc`: type `LONGLONG`, value `Int 1`), is misread: the
    value's indicator byte is taken as the type's third byte, the first value byte (`1`) as the
    indicator, so the value comes back as `NULL`, with 7 bytes left over. -/
theorem bulkReqRead_types_misread :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)]
        (bulkReqEnc ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(0, .int 1)]⟩) =
      .done (some ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(1, .null)]⟩)
        (List.replicate 7 (byte 0)) := by
  rfl

/-- **Crate bug** (one row read): of a two-row request (one parameter, no types), the reader
    returns only the first row's value and leaves the second row in the input. -/
theorem bulkReqRead_first_row_only :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)] (bulkReqEnc ⟨1, 0, [], [(0, .int 1), (0, .int 2)]⟩) =
      .done (some ⟨1, 0, [], [(0, .int 1)]⟩) (bulkValueEnc (0, .int 2)) := by
  rfl

/-- **Crate behaviour** (type merge): an `Int` and a `UInt` for the same parameter give the type
    `LONGLONG UNSIGNED` for the batch, so the server reads a negative `Int` such as `-1` (sent
    as `0xFF…FF`) as `18446744073709551615`. -/
theorem bulkTypes_int_uint :
    bulkTypes [[.int (-1)], [.uint 5]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 128)] := by
  decide

/-- **Crate behaviour** (type merge, a `TODO` in the source): for values of different types the
    first row's type is kept, here `LONGLONG` for a batch that also has `Bytes`. -/
theorem bulkTypes_first_wins :
    bulkTypes [[.int 1], [.bytes [byte 97]]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)] := by
  decide

/-- `add_row`'s bookkeeping (`bulkAddRow`) keeps `BulkBuilder.Inv`. -/
theorem bulkAddRow_inv (b : BulkBuilder) (row : List value.Value) (h : b.Inv) :
    (bulkAddRow b row).2.Inv := by
  obtain ⟨hr, hp, hm⟩ := h
  obtain ⟨sid, wt, wr, rows, pl, ar, np, mx⟩ := b
  simp only at hr hp hm
  -- rows nonempty → arity is some
  have hne : rows ≠ [] → ∃ a, ar = some a := by
    intro hne
    obtain ⟨r, hr'⟩ := List.exists_mem_of_ne_nil rows hne
    exact ⟨_, (hr r hr').symm⟩
  unfold bulkAddRow
  simp only
  split
  · -- mixed arity
    rename_i hneq
    refine ⟨?_, ?_, ?_⟩
    · intro r hrm; cases ar with
      | none => simp at hneq
      | some a => simpa using hr r hrm
    · cases ar with
      | none => simp at hneq
      | some a => simpa using hp
    · exact hm
  · rename_i heq
    simp only [ne_eq, Decidable.not_not] at heq
    -- reduce to `ar = some row.length` with the old `pl` in its normal form
    have key : ∀ (a : Nat), (∀ r ∈ rows, some r.length = some a) →
        (if wt = true ∧ pl = 0 then 2 * row.length else pl) =
          (if wt then 2 * row.length else 0) + (rows.map (fun r => bulkRowLen (r.map Val.ofValue))).sum →
        (rows ≠ [] → 7 + ((if wt then 2 * row.length else 0) +
          (rows.map (fun r => bulkRowLen (r.map Val.ofValue))).sum) ≤ mx) → a = row.length →
        BulkBuilder.Inv (if mx < 7 + (if wt = true ∧ pl = 0 then 2 * row.length else pl) +
              bulkRowLen (List.map Val.ofValue row) then
            (if rows = [] then AddRowOut.tooLarge else AddRowOut.full,
              { stmtId := sid, withTypes := wt, withResults := wr, rows := rows,
                payloadLen := if wt = true ∧ pl = 0 then 2 * row.length else pl,
                arity := some a, namedParams := np, maxPayloadLen := mx : BulkBuilder })
          else
            (AddRowOut.added,
              { stmtId := sid, withTypes := wt, withResults := wr, rows := rows ++ [row],
                payloadLen := (if wt = true ∧ pl = 0 then 2 * row.length else pl) +
                  bulkRowLen (List.map Val.ofValue row),
                arity := some a, namedParams := np, maxPayloadLen := mx : BulkBuilder })).2 := by
      intro a hr' hpl hm' ha
      subst ha
      generalize hS : (rows.map (fun r => bulkRowLen (r.map Val.ofValue))).sum = S at hpl hm'
      rw [hpl]
      by_cases hlt : mx < 7 + ((if wt then 2 * row.length else 0) + S) + bulkRowLen (row.map Val.ofValue)
      · simp only [hlt, ite_true]
        exact ⟨hr', by simp only [Option.getD_some, hS], hm'⟩
      · simp only [hlt, ite_false]
        refine ⟨?_, ?_, ?_⟩
        · intro r hrm
          simp only [List.mem_append, List.mem_singleton] at hrm
          rcases hrm with hrm | rfl
          · exact hr' r hrm
          · rfl
        · simp only [Option.getD_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil, hS]
          omega
        · intro _; simp only; omega
    cases ar with
    | none =>
      have hrn : rows = [] := by
        by_contra hc; obtain ⟨a, ha⟩ := hne hc; simp at ha
      subst hrn
      simp only [Option.getD_none, mul_zero, ite_self, List.map_nil, List.sum_nil, add_zero] at hp
      subst hp
      exact key row.length (by simp) (by cases wt <;> simp) (by simp) rfl
    | some a =>
      simp only [Option.getD_some] at heq hp ⊢
      subst heq
      refine key _ (fun r h' => hr r h') ?_ ?_ rfl
      · cases wt <;> simp only [true_and, Bool.false_eq_true, false_and, ite_false, ite_true] at hp ⊢
        · omega
        · split <;> omega
      · intro hne'; have := hm hne'; omega

private theorem bulkTypes_foldl_length (rows : List (List Val)) : ∀ (ts : List (Nat × Nat)),
    (rows.foldl (fun ts row => List.zipWith bulkMerge ts (row.map bulkTy)) ts).length ≤ ts.length := by
  induction rows with
  | nil => intro ts; simp
  | cons r rs ih =>
    intro ts
    simp only [List.foldl_cons]
    refine le_trans (ih _) ?_
    simp

private theorem bulkTypes_length_le (r0 : List Val) (rs : List (List Val)) :
    (bulkTypes (r0 :: rs)).length ≤ r0.length := by
  simp only [bulkTypes]
  refine le_trans (bulkTypes_foldl_length _ _) ?_
  simp

private theorem bulkValues_length (l : List Val) :
    ((l.map (fun v => (bulkInd v, v))).flatMap bulkValueEnc).length = bulkRowLen l := by
  induction l with
  | nil => simp [bulkRowLen]
  | cons v l ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, ih, bulkRowLen, List.sum_cons]
    simp [bulkValueEnc]; omega

private theorem hasFlag_flags (b : BulkBuilder) :
    hasFlag b.flags SEND_TYPES_TO_SERVER = b.withTypes := by
  unfold BulkBuilder.flags
  cases b.withTypes <;> cases b.withResults <;> decide


/-- With `BulkBuilder.Inv`, the request built from the builder's rows fits in `maxPayloadLen`
    bytes. -/
theorem bulkBuild_fits (b : BulkBuilder) (h : b.Inv) (q : BulkReq)
    (hq : bulkNewOut b.stmtId b.flags (b.rows.map (·.map Val.ofValue)) = .ok q) :
    (bulkReqEnc q).length ≤ b.maxPayloadLen := by
  obtain ⟨hr, hp, hm⟩ := h
  cases hrows : b.rows with
  | nil => rw [hrows] at hq; simp [bulkNewOut] at hq
  | cons r0 rs =>
    rw [hrows] at hq hr hp hm
    have hm' := hm (by simp)
    simp only [bulkNewOut, List.map_cons] at hq
    split at hq
    · rename_i hall
      simp only [BulkNewOut.ok.injEq] at hq
      subst hq
      have ha : b.arity = some r0.length := (hr r0 (by simp)).symm
      rw [ha] at hp
      have hv := bulkValues_length ((r0.map Val.ofValue :: rs.map (·.map Val.ofValue)).flatten)
      have hsum : bulkRowLen ((r0.map Val.ofValue :: rs.map (·.map Val.ofValue)).flatten) =
          ((r0 :: rs).map (fun r => bulkRowLen (r.map Val.ofValue))).sum := by
        simp [bulkRowLen, List.map_flatten, List.sum_flatten, Function.comp_def]
      have ht := bulkTypes_length_le (r0.map Val.ofValue) (rs.map (·.map Val.ofValue))
      simp only [List.length_map] at ht
      simp only [bulkReqEnc, bulkNew, hasFlag_flags, List.length_cons, List.length_append,
        length_leBytes, hv, hsum]
      simp only [Option.getD_some] at hp
      cases hw : b.withTypes
      · simp only [hw, Bool.false_eq_true, ite_false, List.length_nil] at hp ⊢; omega
      · simp only [hw, ite_true, List.length_flatMap] at hp ⊢
        have : ((bulkTypes (r0.map Val.ofValue :: rs.map (·.map Val.ofValue))).map
            (fun t => (bulkTypeEnc t).length)).sum =
            2 * (bulkTypes (r0.map Val.ofValue :: rs.map (·.map Val.ofValue))).length := by
          simp [bulkTypeEnc]; omega
        omega
    · simp at hq

/-- `COM_REGISTER_SLAVE` round trip: the reader reads the protocol layout back (strings of at
    most 255 bytes, numbers in range). -/
theorem regSlaveRead_regSlaveEnc (r : RegSlave)
    (hr : r.serverId < 2 ^ 32 ∧ r.hostname.length ≤ 255 ∧ r.user.length ≤ 255 ∧
      r.password.length ≤ 255 ∧ r.port < 2 ^ 16 ∧ r.rank < 2 ^ 32 ∧ r.masterId < 2 ^ 32)
    (tail : List U8) :
    regSlaveRead (regSlaveEnc r ++ tail) = (some r, tail) := by
  sorry

/-- `COM_BINLOG_DUMP_GTID` round trip (untagged format): the reader reads `gtidDumpEnc` back
    (known flags, numbers in range, 16-byte UUIDs, file name and SID block shorter than `2^32`
    bytes). -/
theorem gtidDumpRead_gtidDumpEnc (g : GtidDump) (hnotag : gtidTagged g.sids = false)
    (hf : g.flags &&& binlogDumpFlagsAll = g.flags) (hsid : g.serverId < 2 ^ 32)
    (hfn : g.filename.length < 2 ^ 32) (hpos : g.pos < 2 ^ 64)
    (hblk : (sidBlock g.sids).length < 2 ^ 32)
    (hs : ∀ s ∈ g.sids, s.uuid.length = 16 ∧ ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) :
    gtidDumpRead (gtidDumpEnc g ++ tail) = .done (some g) tail := by
  sorry

/-- The tagged `n_sids` word the crate writes has format byte `1` and the count in bits 8–55,
    so its own reader recognises it (for fewer than `2^48` SIDs). -/
theorem nSidsHeader_tagged (n : Nat) (hn : n < 2 ^ 48) :
    (nSidsHeader true n).length = 8 ∧ leNat (nSidsHeader true n) / 2 ^ 56 = 1 ∧
    (leNat (nSidsHeader true n) / 2 ^ 8) % 2 ^ 48 = n := by
  sorry

/-- Totality of the bulk value reader: it returns or panics, never `unknown`. -/
theorem bulkValueRead_ne_unknown (ct : constants.ColumnType) (u : Bool) (bs : List U8) :
    bulkValueRead ct u bs ≠ .unknown := by
  unfold bulkValueRead
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · split <;> simp
        · simp

/-- Totality of the bulk row reader: it returns or panics, never `unknown`. -/
theorem bulkValuesRead_ne_unknown (ps : List (constants.ColumnType × Bool)) (bs : List U8) :
    bulkValuesRead ps bs ≠ .unknown := by
  induction ps generalizing bs with
  | nil => simp [bulkValuesRead]
  | cons p ps ih =>
    obtain ⟨ct, u⟩ := p
    have h1 := bulkValueRead_ne_unknown ct u bs
    simp only [bulkValuesRead]
    split
    · rename_i v rest _
      have h2 := ih rest
      split <;> simp_all
    · simp
    · simp
    · simp_all

/-- Totality of the bulk request reader: it returns or panics, never `unknown` (so `deserialize_spec` and `deserialize_panics` of `ComStmtBulkExecuteRequest` cover every input). -/
theorem bulkReqRead_ne_unknown (ps : List (constants.ColumnType × Bool)) (bs : List U8) :
    bulkReqRead ps bs ≠ .unknown := by
  unfold bulkReqRead
  split
  · simp
  · dsimp only
    repeat' split
    all_goals simp_all [bulkValuesRead_ne_unknown]

/-- The interval reader returns or panics, never `unknown`. -/
theorem intervalsRead_ne_unknown (bs : List U8) : intervalsRead bs ≠ .unknown := by
  unfold intervalsRead
  dsimp only
  repeat' split
  all_goals simp

/-- Totality of the untagged SID reader: it returns or panics, never `unknown`. -/
theorem sidRead_ne_unknown (bs : List U8) : sidRead bs ≠ .unknown := by
  unfold sidRead
  repeat' split
  all_goals simp_all [intervalsRead_ne_unknown]

/-- Untagged SIDs are read totally: returned or panicked, never `unknown`. -/
theorem sidsRead_untagged_ne_unknown (n : Nat) (bs : List U8) : sidsRead false n bs ≠ .unknown := by
  induction n generalizing bs with
  | zero => simp [sidsRead]
  | succ n ih =>
    simp only [sidsRead, Bool.false_eq_true, ↓reduceIte]
    repeat' split
    all_goals simp_all [sidRead_ne_unknown]

/-- The tagged SID reader is `unknown` exactly for a SID with a tag of 1 to 32 bytes that is present and valid UTF-8 (where `Tag::new` would check its characters). -/
theorem sidTaggedRead_unknown_iff (bs : List U8) :
    sidTaggedRead bs = .unknown ↔
      16 ≤ bs.length ∧ ∃ tl r, varlenUintDecode (bs.drop 16) = some (tl, r) ∧ 0 < tl ∧ tl ≤ 32 ∧
        tl ≤ r.length ∧ (Trusted.bytesOf (r.take tl)).IsValidUTF8 := by
  unfold sidTaggedRead
  by_cases h16 : bs.length < 16
  · simp [h16]
  · simp only [h16, ite_false]
    rcases hv : varlenUintDecode (bs.drop 16) with _ | ⟨tl, r⟩
    · simp
    · simp only
      by_cases h0 : tl = 0
      · subst h0
        simp only [ite_true]
        constructor
        · intro h
          exfalso
          have := intervalsRead_ne_unknown r
          revert h
          split <;> simp_all
        · rintro ⟨_, tl, r', h, hlt, _⟩
          simp at h; omega
      · simp only [h0, ite_false]
        constructor
        · intro h
          refine ⟨by omega, tl, r, rfl, by omega, ?_⟩
          by_cases h1 : r.length < tl
          · simp [h1] at h
          · by_cases h2 : (Trusted.bytesOf (r.take tl)).IsValidUTF8
            · by_cases h3 : 32 < tl
              · simp [h1, h2, h3] at h
              · exact ⟨by omega, by omega, h2⟩
            · simp [h1, h2] at h
        · rintro ⟨_, tl', r', h, _, h32, hle, hu⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [show ¬ r.length < tl by omega, hu, show ¬ 32 < tl by omega]

/-- Untagged SID lists are read totally, and a tagged one is `unknown` only through a SID whose
    reading is `unknown` (`sidTaggedRead_unknown_iff`), read from a suffix of the input. -/
theorem sidsRead_unknown (tagged : Bool) (n : Nat) (bs : List U8)
    (h : sidsRead tagged n bs = .unknown) :
    tagged = true ∧ ∃ bs', bs' <:+ bs ∧ sidTaggedRead bs' = .unknown := by
  sorry

/-- `gtidDumpRead` is `unknown` only through a tagged SID, inside the input, whose tag has 1 to
    32 bytes and is valid UTF-8 (`sidTaggedRead_unknown_iff`); every other input is returned or
    panics. -/
theorem gtidDumpRead_unknown (bs : List U8) (h : gtidDumpRead bs = .unknown) :
    ∃ bs', bs' <:+: bs ∧ sidTaggedRead bs' = .unknown := by
  sorry

/-- The values of a request made by `ComStmtBulkExecuteRequest::new` carry the indicators the
    protocol defines: `NULL` (1) exactly for `NULL`, else `NONE` (0). -/
theorem bulkNew_indicators (stmtId flags : Nat) (rows : List (List Val)) :
    ∀ iv ∈ (bulkNew stmtId flags rows).values, (iv.1 = 0 ∨ iv.1 = 1) ∧ (iv.1 = 1 ↔ iv.2 = .null) := by
  intro iv hiv
  simp only [bulkNew, List.mem_map] at hiv
  obtain ⟨v, _, rfl⟩ := hiv
  cases v <;> simp [bulkInd]

private theorem bulkValueRead_enc (ct : constants.ColumnType) (u : Bool) (v : value.Value)
    (hc : Val.ofValue v = .null ∨ binCompatible (Val.ofValue v) ct) (t : List U8) :
    bulkValueRead ct u (bulkValueEnc (bulkInd (Val.ofValue v), Val.ofValue v) ++ t) =
      .done (some (bulkInd (Val.ofValue v), binNorm u (Val.ofValue v))) t := by
  by_cases hn : Val.ofValue v = .null
  · have h1 : (byte 1).val = 1 := by decide
    rw [hn]; simp [bulkValueEnc, bulkInd, bulkValueRead, binEnc, binNorm, h1]
  · have hc' : binCompatible (Val.ofValue v) ct := hc.resolve_left hn
    have hi : bulkInd (Val.ofValue v) = 0 := by
      revert hn; cases Val.ofValue v <;> simp [bulkInd]
    have hs : binSupported ct = true := by
      revert hc'; cases Val.ofValue v <;> cases ct <;> simp [binCompatible, binSupported, isLenencStrType]
    have h0 : (byte 0).val = 0 := by decide
    rw [hi]
    simp [h0, bulkValueEnc, bulkValueRead, hs, binRead_binEnc v ct u t hc']

private theorem bulkValuesRead_enc : ∀ (ps : List (constants.ColumnType × Bool)) (row : List value.Value)
    (_ : ps.length = row.length)
    (_ : ∀ p ∈ ps.zip row, Val.ofValue p.2 = .null ∨ binCompatible (Val.ofValue p.2) p.1.1)
    (tail : List U8),
    bulkValuesRead ps ((row.map (fun v => (bulkInd (Val.ofValue v), Val.ofValue v))).flatMap bulkValueEnc ++ tail) =
      .done (some ((ps.zip row).map (fun p =>
        (bulkInd (Val.ofValue p.2), binNorm p.1.2 (Val.ofValue p.2))))) tail
  | [], [], _, _, _ => by simp [bulkValuesRead]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | (ct, u) :: ps, v :: row, hl, hc, tail => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have h1 := hc ((ct, u), v) (by simp)
    have ih := bulkValuesRead_enc ps row hl (fun p hp => hc p (by simp [hp])) tail
    simp only [List.map_cons, List.flatMap_cons, List.append_assoc, List.zip_cons_cons]
    simp only [bulkValuesRead, bulkValueRead_enc ct u v h1, ih]


/-- The one case the bulk request reader reads correctly: without `SEND_TYPES_TO_SERVER`, a
    single row of values whose types the reader is given (each value `NULL` or compatible with
    its parameter's column type), is read back, up to the binary decoder's normalisation
    `binNorm`. -/
theorem bulkReqRead_one_row (sid f : Nat) (hsid : sid < 2 ^ 32) (hf : f = 0 ∨ f = SEND_UNIT_RESULTS)
    (ps : List (constants.ColumnType × Bool)) (row : List value.Value) (hlen : ps.length = row.length)
    (hc : ∀ p ∈ ps.zip row, Val.ofValue p.2 = .null ∨ binCompatible (Val.ofValue p.2) p.1.1)
    (tail : List U8) :
    bulkReqRead ps (bulkReqEnc ⟨sid, f, [], row.map (fun v => (bulkInd (Val.ofValue v), Val.ofValue v))⟩ ++ tail) =
      .done (some ⟨sid, f, [], (ps.zip row).map (fun p =>
        (bulkInd (Val.ofValue p.2), binNorm p.1.2 (Val.ofValue p.2)))⟩) tail := by
  have hv := bulkValuesRead_enc ps row hlen hc tail
  have hf2 : leNat (leBytes 2 f) = f := by rw [leNat_leBytes]; rcases hf with rfl | rfl <;> decide
  have hs4 : leNat (leBytes 4 sid) = sid := by rw [leNat_leBytes]; omega
  have hfl : hasFlag f SEND_TYPES_TO_SERVER = false := by rcases hf with rfl | rfl <;> decide
  have hfm : (f &&& (SEND_UNIT_RESULTS ||| SEND_TYPES_TO_SERVER) ≠ f) = False := by
    rcases hf with rfl | rfl <;> decide
  simp only [bulkReqEnc, hfl, Bool.false_eq_true, ite_false, List.append_nil, List.cons_append,
    bulkReqRead, List.append_assoc]
  have hb : (byte 0xFA).val = 0xFA := by decide
  have h6 : ∀ x, ¬ (4 + (2 + x) < 6) := by omega
  have h4 : ∀ x, ¬ (4 + (2 + x) < 4) := by omega
  have hd : ∀ X : List U8, List.drop 6 (leBytes 4 sid ++ (leBytes 2 f ++ X)) = X := by
    intro X; rw [← List.append_assoc, List.drop_left' (by simp)]
  simp [h6, h4, hb, hs4, hf2, hfm, hfl, hd, hv]

end Defs
