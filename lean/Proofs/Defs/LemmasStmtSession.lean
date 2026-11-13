import Defs

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
  sorry

/-- Session state round trip: a sequence of entries in the protocol layout is read back. -/
theorem ssInfos_ssInfoEnc (is : List SsInfo) (h : ∀ i ∈ is, i.2.length < 2 ^ 64) :
    ssInfos (is.flatMap ssInfoEnc) = some is := by
  sorry

/-- **Crate bug** (bulk types read from 3 bytes): a one-parameter request with its type, as the
    crate itself serializes it (`bulkReqEnc`: type `LONGLONG`, value `Int 1`), is misread: the
    value's indicator byte is taken as the type's third byte, the first value byte (`1`) as the
    indicator, so the value comes back as `NULL`, with 7 bytes left over. -/
theorem bulkReqRead_types_misread :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)]
        (bulkReqEnc ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(0, .int 1)]⟩) =
      .done (some ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(1, .null)]⟩)
        (List.replicate 7 (byte 0)) := by
  sorry

/-- **Crate bug** (one row read): of a two-row request (one parameter, no types), the reader
    returns only the first row's value and leaves the second row in the input. -/
theorem bulkReqRead_first_row_only :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)] (bulkReqEnc ⟨1, 0, [], [(0, .int 1), (0, .int 2)]⟩) =
      .done (some ⟨1, 0, [], [(0, .int 1)]⟩) (bulkValueEnc (0, .int 2)) := by
  sorry

/-- **Crate behaviour** (type merge): an `Int` and a `UInt` for the same parameter give the type
    `LONGLONG UNSIGNED` for the batch, so the server reads a negative `Int` such as `-1` (sent
    as `0xFF…FF`) as `18446744073709551615`. -/
theorem bulkTypes_int_uint :
    bulkTypes [[.int (-1)], [.uint 5]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 128)] := by
  sorry

/-- **Crate behaviour** (type merge, a `TODO` in the source): for values of different types the
    first row's type is kept, here `LONGLONG` for a batch that also has `Bytes`. -/
theorem bulkTypes_first_wins :
    bulkTypes [[.int 1], [.bytes [byte 97]]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)] := by
  sorry

/-- `add_row`'s bookkeeping (`bulkAddRow`) keeps `BulkBuilder.Inv`. -/
theorem bulkAddRow_inv (b : BulkBuilder) (row : List value.Value) (h : b.Inv) :
    (bulkAddRow b row).2.Inv := by
  sorry

/-- With `BulkBuilder.Inv`, the request built from the builder's rows fits in `maxPayloadLen`
    bytes. -/
theorem bulkBuild_fits (b : BulkBuilder) (h : b.Inv) (q : BulkReq)
    (hq : bulkNewOut b.stmtId b.flags (b.rows.map (·.map Val.ofValue)) = .ok q) :
    (bulkReqEnc q).length ≤ b.maxPayloadLen := by
  sorry

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
  sorry

end Defs
