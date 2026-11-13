import Proofs.Defs.LemmasBinlogEvents

/-!
# Facts about the binlog-event definitions (`lean/Defs/BinlogEvents.lean`)
    Pure-Lean properties a signer should read: header and fixed-text
    lengths; each format reader inverts its encoder (FDE, query, GTID, previous GTIDs, table map,
    rows); worked examples of the status-variable walk and the metadata walk; the upstream bugs
    on examples (`Q_UPDATED_DB_NAMES`, the count 254, the non-fused iterator, the table map and
    GTID lengths, the v1 rows length). (Facts about the enum codes are with `Defs/BinlogCore.lean`.)
    Proofs: `Proofs/Defs/LemmasBinlogEvents.lean`.

    **Trusted axioms:** none.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ### Lemmas -/

/-- The common header is 19 bytes. -/
recall evHeaderEnc_length (h : binlog.events.BinlogEventHeader) : (evHeaderEnc h).length = 19

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.evHeaderEnc_length
/-- A fixed-length text has exactly its length. -/
recall fixedText_length (L : Nat) (s : List U8) : (fixedText L s).length = L

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fixedText_length
/-- Without a post-header array, a query event's post-header is 13 bytes and a rows v2 event's 10. -/
recall postHeaderLen_query_default : postHeaderLen [] .QUERY_EVENT = 13 ∧ postHeaderLen [] .WRITE_ROWS_EVENT = 10

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.postHeaderLen_query_default
/-- The FDE reader inverts the encoder (the server version padded to 50 bytes). -/
recall fdeRead_fdeEnc (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    fdeRead (fdeEnc e) = some ({ fdeView e with serverVersion := fixedText 50 (cowList e.server_version.1) }, [])

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.fdeRead_fdeEnc
/-- The query reader inverts the encoder, for consistent lengths and a post-header of at most 13 bytes. -/
recall queryRead_queryEnc (e : binlog.events.query_event.QueryEvent) (p : Nat) (hp : p ≤ 13)
    (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length) (hsv' : (cowList e.status_vars.1).length ≤ 65535)
    (hs : e.schema_len.1.val = (cowList e.schema.1).length) (hs' : (cowList e.schema.1).length ≤ 255) :
    queryRead p (queryEnc e) = some (queryView e, [])

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.queryRead_queryEnc
/-- An example walk: `Q_FLAGS2_CODE` (4 bytes), then `Q_CATALOG_NZ_CODE` with a 2-byte name, then an unknown key 99 stops the walk. -/
recall statusVarsOf_example : statusVarsOf [byte 0, byte 1, byte 2, byte 3, byte 4, byte 6, byte 2, byte 97, byte 98, byte 99, byte 7] =
      [(0, [byte 1, byte 2, byte 3, byte 4]), (6, [byte 2, byte 97, byte 98])]

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.statusVarsOf_example
/-- The `Q_UPDATED_DB_NAMES` bug on an example: two names `a`, `b`; the format gives both, the crate `a` and an empty name. -/
recall dbNamesCrate_ne_dbNames : dbNames 2 [byte 97, byte 0, byte 98, byte 0] = some [[byte 97], [byte 98]] ∧
      dbNamesCrate 2 [byte 97, byte 0, byte 98, byte 0] = some [[byte 97], []]

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.dbNamesCrate_ne_dbNames
/-- The GTID reader inverts the encoder (untagged, with the logical-clock part, timestamps below `2^55` / `2^56`, immediate server version below `2^31`). -/
recall gtidRead_gtidEnc (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hs : e.immediate_server_version.1.val < 2 ^ 31) (tail : List U8) :
    gtidRead (gtidEnc e ++ tail) = some (gtidView e, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidRead_gtidEnc
/-- With the logical-clock part, the crate's GTID length is the encoded length. -/
recall gtidLenCrate_eq (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode.isSome) :
    gtidLenCrate e = min (gtidEnc e).length evLenCap

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidLenCrate_eq
/-- Without it, the encoding is 25 bytes but the crate's length at least 54. -/
recall gtidLenCrate_ne (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode = none) :
    (gtidEnc e).length = 25 ∧ 54 ≤ gtidLenCrate e

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.gtidLenCrate_ne
/-- A `Q_UPDATED_DB_NAMES` count of 254 (`OVER_MAX_DBS_IN_EVENT_MTS`, no names follow) stops the walk: the `Q_FLAGS2_CODE` variable after it is lost. -/
recall statusVarsOf_over_max_dbs : statusVarsOf [byte 12, byte 254, byte 0, byte 1, byte 2, byte 3, byte 4] = []

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.statusVarsOf_over_max_dbs
/-- The walk from inside a failed variable: on `[11, 16, 1]` the walk from 0 is empty (`Q_INVOKER` truncated) but from 1 it yields `Q_EXPLICIT_DEFAULTS_FOR_TIMESTAMP`. -/
recall statusVarsIter_not_fused : svStep [byte 11, byte 16, byte 1] 0 = none ∧ svStep [byte 11, byte 16, byte 1] 1 = some ((16, [byte 1]), 3)

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.statusVarsIter_not_fused
/-- The untagged previous-GTIDs reader inverts the encoder (fewer than `2^56` SIDs). -/
recall pgRead_pgEnc (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hl : e.sids.length < 2 ^ 56) (tail : List U8) :
    pgRead (pgEnc e ++ tail) = some (e.sids.val.map pgSidView, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.pgRead_pgEnc
/-- The table map reader inverts the encoder for a consistent event (post-header not 6 bytes, table id below `2^48`). -/
recall tmRead_tmEnc (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (p : Nat) (hp : p ≠ 6) : tmRead p (tmEnc e) = some (tmView e, [])

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.tmRead_tmEnc
/-- The table map length bug on the smallest case: a consistent event without columns is counted one byte too long. -/
recall tmLenCrate_zero (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (h0 : e.columns_count.1.val = 0)
    (hcap : (tmEnc e).length + 1 ≤ evLenCap) : tmLenCrate e = (tmEnc e).length + 1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.tmLenCrate_zero
/-- Metadata walk on an example: columns `LONG` (none), `VARCHAR` (2 bytes), `BLOB` (1 byte). -/
recall tmMetaAt_example : tmMetaAt [byte 3, byte 15, byte 252] [byte 10, byte 0, byte 4] 1 = some [byte 10, byte 0] ∧
      tmMetaAt [byte 3, byte 15, byte 252] [byte 10, byte 0, byte 4] 2 = some [byte 4]

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.tmMetaAt_example
/-- The rows reader inverts the encoder for a consistent event, with post-header lengths that agree with its type. -/
recall rowsRead_rowsEnc (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (p pw : Nat) (hp : p ≠ 6) (hv : p = pw ↔ rowsIsV2 e.event_type = true) :
    rowsRead e.event_type p pw (rowsEnc e) = some (rowsView e, [])

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.rowsRead_rowsEnc
/-- The rows length quirk: for a consistent v1 event the crate's length is 2 more than the encoding (under the cap). -/
recall rowsLenCrate_v1 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) : rowsLenCrate e = (rowsEnc e).length + 2

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.rowsLenCrate_v1
end Defs
