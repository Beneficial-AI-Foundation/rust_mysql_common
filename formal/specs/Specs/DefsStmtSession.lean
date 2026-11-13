import Proofs.Defs.LemmasStmtSession

/-!
# Facts about the statement, session-state and replication definitions
  (`formal/specs/Defs/CmdPackets.lean`, `formal/specs/Defs/SessionState.lean`, `formal/specs/Defs/BinlogCmd.lean`)
    Pure-Lean properties a signer should read: the readers invert the protocol encodings
    (`COM_STMT_PREPARE_OK`, session state entries, `COM_REGISTER_SLAVE`, `COM_BINLOG_DUMP_GTID`
    untagged, and tagged with valid tags); the crate's tagged `n_sids` word is recognised by its reader; the
    bulk builder's bookkeeping keeps requests within the packet limit; and concrete examples of
    the bulk-execute bugs and quirks (types read from 3 bytes, only the first row read, type
    merging). Totality: the bulk, SID (both formats) and GTID readers never give `unknown`
    (since formal/trusted/patches/156 the tag check is bytewise, `tagBytesValid`). Proofs:
    `Proofs/Defs/LemmasStmtSession.lean` (all proved).

    **Trusted axioms:** none.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ### Lemmas -/

/-- `COM_STMT_PREPARE_OK` round trip: the reader reads the protocol layout back (fields in
    range). -/
recall stmtOkRead_stmtOkEnc (s : StmtOk)
    (hs : s.stmtId < 2 ^ 32 ∧ s.numColumns < 2 ^ 16 ∧ s.numParams < 2 ^ 16 ∧ s.warnings < 2 ^ 16)
    (tail : List U8) :
    stmtOkRead (stmtOkEnc s ++ tail) = (some s, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.stmtOkRead_stmtOkEnc
/-- Session state round trip: a sequence of entries in the protocol layout is read back. -/
recall ssInfos_ssInfoEnc (is : List SsInfo) (h : ∀ i ∈ is, i.2.length < 2 ^ 64) :
    ssInfos (is.flatMap ssInfoEnc) = some is

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.ssInfos_ssInfoEnc
/-- **Crate bug** (bulk types read from 3 bytes): a one-parameter request with its type, as the
    crate itself serializes it (`bulkReqEnc`: type `LONGLONG`, value `Int 1`), is misread: the
    value's indicator byte is taken as the type's third byte, the first value byte (`1`) as the
    indicator, so the value comes back as `NULL`, with 7 bytes left over. -/
recall bulkReqRead_types_misread :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)]
        (bulkReqEnc ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(0, .int 1)]⟩) =
      .done (some ⟨1, SEND_TYPES_TO_SERVER, [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)], [(1, .null)]⟩)
        (List.replicate 7 (byte 0))

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkReqRead_types_misread
/-- **Crate bug** (one row read): of a two-row request (one parameter, no types), the reader
    returns only the first row's value and leaves the second row in the input. -/
recall bulkReqRead_first_row_only :
    bulkReqRead [(.MYSQL_TYPE_LONGLONG, false)] (bulkReqEnc ⟨1, 0, [], [(0, .int 1), (0, .int 2)]⟩) =
      .done (some ⟨1, 0, [], [(0, .int 1)]⟩) (bulkValueEnc (0, .int 2))

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkReqRead_first_row_only
/-- **Crate behaviour** (type merge): an `Int` and a `UInt` for the same parameter give the type
    `LONGLONG UNSIGNED` for the batch, so the server reads a negative `Int` such as `-1` (sent
    as `0xFF…FF`) as `18446744073709551615`. -/
recall bulkTypes_int_uint :
    bulkTypes [[.int (-1)], [.uint 5]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 128)]

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkTypes_int_uint
/-- **Crate behaviour** (type merge, a `TODO` in the source): for values of different types the
    first row's type is kept, here `LONGLONG` for a batch that also has `Bytes`. -/
recall bulkTypes_first_wins :
    bulkTypes [[.int 1], [.bytes [byte 97]]] = [(columnTypeCode .MYSQL_TYPE_LONGLONG, 0)]

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkTypes_first_wins
/-- `add_row`'s bookkeeping (`bulkAddRow`) keeps `BulkBuilder.Inv`. -/
recall bulkAddRow_inv (b : BulkBuilder) (row : List value.Value) (h : b.Inv) :
    (bulkAddRow b row).2.Inv

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkAddRow_inv
/-- With `BulkBuilder.Inv`, the request built from the builder's rows fits in `maxPayloadLen`
    bytes. -/
recall bulkBuild_fits (b : BulkBuilder) (h : b.Inv) (q : BulkReq)
    (hq : bulkNewOut b.stmtId b.flags (b.rows.map (·.map Val.ofValue)) = .ok q) :
    (bulkReqEnc q).length ≤ b.maxPayloadLen

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkBuild_fits
/-- `COM_REGISTER_SLAVE` round trip: the reader reads the protocol layout back (strings of at
    most 255 bytes, numbers in range). -/
recall regSlaveRead_regSlaveEnc (r : RegSlave)
    (hr : r.serverId < 2 ^ 32 ∧ r.hostname.length ≤ 255 ∧ r.user.length ≤ 255 ∧
      r.password.length ≤ 255 ∧ r.port < 2 ^ 16 ∧ r.rank < 2 ^ 32 ∧ r.masterId < 2 ^ 32)
    (tail : List U8) :
    regSlaveRead (regSlaveEnc r ++ tail) = (some r, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.regSlaveRead_regSlaveEnc
/-- `COM_BINLOG_DUMP_GTID` round trip (untagged format): the reader reads `gtidDumpEnc` back
    (known flags, numbers in range, 16-byte UUIDs, file name and SID block shorter than `2^32`
    bytes). -/
recall gtidDumpRead_gtidDumpEnc (g : GtidDump) (hnotag : gtidTagged g.sids = false)
    (hf : g.flags &&& binlogDumpFlagsAll = g.flags) (hsid : g.serverId < 2 ^ 32)
    (hfn : g.filename.length < 2 ^ 32) (hpos : g.pos < 2 ^ 64)
    (hblk : (sidBlock g.sids).length < 2 ^ 32)
    (hs : ∀ s ∈ g.sids, s.uuid.length = 16 ∧ ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) :
    gtidDumpRead (gtidDumpEnc g ++ tail) = .done (some g) tail

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidDumpRead_gtidDumpEnc
/-- `COM_BINLOG_DUMP_GTID` round trip, with or without tags: the reader reads `gtidDumpEnc` back
    (known flags, numbers in range, 16-byte UUIDs, every tag present valid (`tagBytesValid`), file
    name and SID block shorter than `2^32` bytes). -/
recall gtidDumpRead_gtidDumpEnc_tagged (g : GtidDump)
    (hf : g.flags &&& binlogDumpFlagsAll = g.flags) (hsid : g.serverId < 2 ^ 32)
    (hfn : g.filename.length < 2 ^ 32) (hpos : g.pos < 2 ^ 64)
    (hblk : (sidBlock g.sids).length < 2 ^ 32)
    (hs : ∀ s ∈ g.sids, s.uuid.length = 16 ∧ (∀ t, s.tag = some t → tagBytesValid t = true) ∧
      ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) :
    gtidDumpRead (gtidDumpEnc g ++ tail) = .done (some g) tail

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidDumpRead_gtidDumpEnc_tagged
/-- The tagged `n_sids` word the crate writes has format byte `1` and the count in bits 8–55,
    so its own reader recognises it (for fewer than `2^48` SIDs). -/
recall nSidsHeader_tagged (n : Nat) (hn : n < 2 ^ 48) :
    (nSidsHeader true n).length = 8 ∧ leNat (nSidsHeader true n) / 2 ^ 56 = 1 ∧
    (leNat (nSidsHeader true n) / 2 ^ 8) % 2 ^ 48 = n

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.nSidsHeader_tagged
/-- Totality of the bulk value reader: it returns or panics, never `unknown`. -/
recall bulkValueRead_ne_unknown (ct : constants.ColumnType) (u : Bool) (bs : List U8) :
    bulkValueRead ct u bs ≠ .unknown

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkValueRead_ne_unknown
/-- Totality of the bulk row reader: it returns or panics, never `unknown`. -/
recall bulkValuesRead_ne_unknown (ps : List (constants.ColumnType × Bool)) (bs : List U8) :
    bulkValuesRead ps bs ≠ .unknown

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkValuesRead_ne_unknown
/-- Totality of the bulk request reader: it returns or panics, never `unknown` (so `deserialize_spec` and `deserialize_panics` of `ComStmtBulkExecuteRequest` cover every input). -/
recall bulkReqRead_ne_unknown (ps : List (constants.ColumnType × Bool)) (bs : List U8) :
    bulkReqRead ps bs ≠ .unknown

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkReqRead_ne_unknown
/-- The interval reader returns or panics, never `unknown`. -/
recall intervalsRead_ne_unknown (bs : List U8) : intervalsRead bs ≠ .unknown

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.intervalsRead_ne_unknown
/-- Totality of the untagged SID reader: it returns or panics, never `unknown`. -/
recall sidRead_ne_unknown (bs : List U8) : sidRead bs ≠ .unknown

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sidRead_ne_unknown
/-- Untagged SIDs are read totally: returned or panicked, never `unknown`. -/
recall sidsRead_untagged_ne_unknown (n : Nat) (bs : List U8) : sidsRead false n bs ≠ .unknown

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sidsRead_untagged_ne_unknown
/-- Totality of the tagged SID reader: it returns or panics, never `unknown` (the tag check is
    modelled, `tagBytesValid`). -/
recall sidTaggedRead_ne_unknown (bs : List U8) : sidTaggedRead bs ≠ .unknown

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sidTaggedRead_ne_unknown
/-- SIDs are read totally, in either format: returned or panicked, never `unknown`. -/
recall sidsRead_ne_unknown (tagged : Bool) (n : Nat) (bs : List U8) :
    sidsRead tagged n bs ≠ .unknown

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.sidsRead_ne_unknown
/-- Totality of the `COM_BINLOG_DUMP_GTID` reader: it returns or panics, never `unknown` (so
    `deserialize_spec` and `deserialize_panics` of `ComBinlogDumpGtid` cover every input). -/
recall gtidDumpRead_ne_unknown (bs : List U8) : gtidDumpRead bs ≠ .unknown

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidDumpRead_ne_unknown
/-- The values of a request made by `ComStmtBulkExecuteRequest::new` carry the indicators the
    protocol defines: `NULL` (1) exactly for `NULL`, else `NONE` (0). -/
recall bulkNew_indicators (stmtId flags : Nat) (rows : List (List Val)) :
    ∀ iv ∈ (bulkNew stmtId flags rows).values, (iv.1 = 0 ∨ iv.1 = 1) ∧ (iv.1 = 1 ↔ iv.2 = .null)

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkNew_indicators
/-- The one case the bulk request reader reads correctly: without `SEND_TYPES_TO_SERVER`, a
    single row of values whose types the reader is given (each value `NULL` or compatible with
    its parameter's column type), is read back, up to the binary decoder's normalisation
    `binNorm`. -/
recall bulkReqRead_one_row (sid f : Nat) (hsid : sid < 2 ^ 32) (hf : f = 0 ∨ f = SEND_UNIT_RESULTS)
    (ps : List (constants.ColumnType × Bool)) (row : List value.Value) (hlen : ps.length = row.length)
    (hc : ∀ p ∈ ps.zip row, Val.ofValue p.2 = .null ∨ binCompatible (Val.ofValue p.2) p.1.1)
    (tail : List U8) :
    bulkReqRead ps (bulkReqEnc ⟨sid, f, [], row.map (fun v => (bulkInd (Val.ofValue v), Val.ofValue v))⟩ ++ tail) =
      .done (some ⟨sid, f, [], (ps.zip row).map (fun p =>
        (bulkInd (Val.ofValue p.2), binNorm p.1.2 (Val.ofValue p.2)))⟩) tail

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.bulkReqRead_one_row
end Defs
