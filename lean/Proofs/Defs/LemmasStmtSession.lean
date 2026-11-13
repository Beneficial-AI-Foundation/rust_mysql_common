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

end Defs
