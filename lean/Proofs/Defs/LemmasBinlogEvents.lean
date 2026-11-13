import Defs
import Proofs.Util.BinlogEvHdr

/-! Facts about the binlog-event definitions (`lean/Defs/BinlogEvents.lean`) (spec file:
`Specs/DefsBinlogEvents.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The common header is 19 bytes. -/
theorem evHeaderEnc_length (h : binlog.events.BinlogEventHeader) : (evHeaderEnc h).length = 19 := by
  exact mysql_common.EvHdrUtil.evHeaderEnc_len h

/-- A fixed-length text has exactly its length. -/
theorem fixedText_length (L : Nat) (s : List U8) : (fixedText L s).length = L := by
  simp only [fixedText, List.length_append, List.length_take, List.length_replicate]; omega

/-- Without a post-header array, a query event's post-header is 13 bytes and a rows v2 event's 10. -/
theorem postHeaderLen_query_default : postHeaderLen [] .QUERY_EVENT = 13 ∧ postHeaderLen [] .WRITE_ROWS_EVENT = 10 := by
  exact ⟨rfl, rfl⟩

/-- The FDE reader inverts the encoder (the server version padded to 50 bytes). -/
theorem fdeRead_fdeEnc (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    fdeRead (fdeEnc e) = some ({ fdeView e with serverVersion := fixedText 50 (cowList e.server_version.1) }, []) := by
  sorry

/-- The query reader inverts the encoder, for consistent lengths and a post-header of at most 13 bytes. -/
theorem queryRead_queryEnc (e : binlog.events.query_event.QueryEvent) (p : Nat) (hp : p ≤ 13)
    (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length) (hsv' : (cowList e.status_vars.1).length ≤ 65535)
    (hs : e.schema_len.1.val = (cowList e.schema.1).length) (hs' : (cowList e.schema.1).length ≤ 255) :
    queryRead p (queryEnc e) = some (queryView e, []) := by
  sorry

/-- An example walk: `Q_FLAGS2_CODE` (4 bytes), then `Q_CATALOG_NZ_CODE` with a 2-byte name, then an unknown key 99 stops the walk. -/
theorem statusVarsOf_example : statusVarsOf [byte 0, byte 1, byte 2, byte 3, byte 4, byte 6, byte 2, byte 97, byte 98, byte 99, byte 7] =
      [(0, [byte 1, byte 2, byte 3, byte 4]), (6, [byte 2, byte 97, byte 98])] := by
  decide

/-- The `Q_UPDATED_DB_NAMES` bug on an example: two names `a`, `b`; the format gives both, the crate `a` and an empty name. -/
theorem dbNamesCrate_ne_dbNames : dbNames 2 [byte 97, byte 0, byte 98, byte 0] = some [[byte 97], [byte 98]] ∧
      dbNamesCrate 2 [byte 97, byte 0, byte 98, byte 0] = some [[byte 97], []] := by
  decide

/-- The GTID reader inverts the encoder (untagged, with the logical-clock part, timestamps below `2^55` / `2^56`, immediate server version below `2^31`). -/
theorem gtidRead_gtidEnc (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hs : e.immediate_server_version.1.val < 2 ^ 31) (tail : List U8) :
    gtidRead (gtidEnc e ++ tail) = some (gtidView e, tail) := by
  sorry

/-- With the logical-clock part, the crate's GTID length is the encoded length. -/
theorem gtidLenCrate_eq (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode.isSome) :
    gtidLenCrate e = min (gtidEnc e).length evLenCap := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hlc
  have hs : e.sid.val.length = 16 := by simp
  simp only [gtidLenCrate, gtidEnc, hc, List.length_append, List.length_cons, List.length_nil, hs,
    PBUtil.length_leBytes]
  split_ifs <;> simp <;> omega

/-- Without it, the encoding is 25 bytes but the crate's length at least 54. -/
theorem gtidLenCrate_ne (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode = none) :
    (gtidEnc e).length = 25 ∧ 54 ≤ gtidLenCrate e := by
  have hs : e.sid.val.length = 16 := by simp
  have hl : 1 ≤ (lenencInt e.tx_length.1.val).length := by unfold lenencInt; split_ifs <;> simp
  refine ⟨by simp [gtidEnc, hlc, hs, PBUtil.length_leBytes], ?_⟩
  simp only [gtidLenCrate, evLenCap]
  split_ifs <;> omega

/-- A `Q_UPDATED_DB_NAMES` count of 254 (`OVER_MAX_DBS_IN_EVENT_MTS`, no names follow) stops the walk: the `Q_FLAGS2_CODE` variable after it is lost. -/
theorem statusVarsOf_over_max_dbs : statusVarsOf [byte 12, byte 254, byte 0, byte 1, byte 2, byte 3, byte 4] = [] := by
  decide

/-- The walk from inside a failed variable: on `[11, 16, 1]` the walk from 0 is empty (`Q_INVOKER` truncated) but from 1 it yields `Q_EXPLICIT_DEFAULTS_FOR_TIMESTAMP`. -/
theorem statusVarsIter_not_fused : svStep [byte 11, byte 16, byte 1] 0 = none ∧ svStep [byte 11, byte 16, byte 1] 1 = some ((16, [byte 1]), 3) := by
  decide

/-- The untagged previous-GTIDs reader inverts the encoder (fewer than `2^56` SIDs). -/
theorem pgRead_pgEnc (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hl : e.sids.length < 2 ^ 56) (tail : List U8) :
    pgRead (pgEnc e ++ tail) = some (e.sids.val.map pgSidView, tail) := by
  sorry

/-- The table map reader inverts the encoder for a consistent event (post-header not 6 bytes, table id below `2^48`). -/
theorem tmRead_tmEnc (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (p : Nat) (hp : p ≠ 6) : tmRead p (tmEnc e) = some (tmView e, []) := by
  sorry

/-- The table map length bug on the smallest case: a consistent event without columns is counted one byte too long. -/
theorem tmLenCrate_zero (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (h0 : e.columns_count.1.val = 0)
    (hcap : (tmEnc e).length + 1 ≤ evLenCap) : tmLenCrate e = (tmEnc e).length + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [h0] at h3 h4
  have h3' : cowList e.columns_type.1 = [] := List.length_eq_zero_iff.mp h3
  have h4' : cowList e.null_bitmask.1 = [] := List.length_eq_zero_iff.mp (by simpa using h4)
  simp only [tmLenCrate, tmEnc, h0, h3', h4', u8Str, List.length_append, List.length_cons, List.length_take,
    List.length_nil, PBUtil.length_leBytes] at hcap ⊢
  simp only [h0, Nat.reduceAdd, Nat.reduceDiv] at *
  omega

/-- Metadata walk on an example: columns `LONG` (none), `VARCHAR` (2 bytes), `BLOB` (1 byte). -/
theorem tmMetaAt_example : tmMetaAt [byte 3, byte 15, byte 252] [byte 10, byte 0, byte 4] 1 = some [byte 10, byte 0] ∧
      tmMetaAt [byte 3, byte 15, byte 252] [byte 10, byte 0, byte 4] 2 = some [byte 4] := by
  have c3 : columnTypeOfCode 3 = some .MYSQL_TYPE_LONG := rfl
  have c15 : columnTypeOfCode 15 = some .MYSQL_TYPE_VARCHAR := rfl
  have c252 : columnTypeOfCode 252 = some .MYSQL_TYPE_BLOB := rfl
  have b3 : (byte 3).val = 3 := rfl
  have b15 : (byte 15).val = 15 := rfl
  have b252 : (byte 252).val = 252 := rfl
  constructor <;> simp [tmMetaAt, tmColumnMeta, c3, c15, c252, b3, b15, b252, getMetadataLen, takeExact]

/-- The rows reader inverts the encoder for a consistent event, with post-header lengths that agree with its type. -/
theorem rowsRead_rowsEnc (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (p pw : Nat) (hp : p ≠ 6) (hv : p = pw ↔ rowsIsV2 e.event_type = true) :
    rowsRead e.event_type p pw (rowsEnc e) = some (rowsView e, []) := by
  sorry

/-- The rows length quirk: for a consistent v1 event the crate's length is 2 more than the encoding (under the cap). -/
theorem rowsLenCrate_v1 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) : rowsLenCrate e = (rowsEnc e).length + 2 := by
  obtain ⟨c1, c2, h3, h4⟩ := hc
  have hex := c2 h1
  have hn : e.num_columns.1.val < 2 ^ 64 := by scalar_tac
  have hbl : (e.num_columns.1.val + 7) / 8 ≤ 2 ^ 61 := by omega
  simp only [rowsLenCrate, rowsEnc, h1, hex, Bool.false_eq_true, ite_false, List.length_append, List.length_nil,
    PBUtil.length_leBytes] at hcap ⊢
  cases hb : e.columns_before_image <;> cases ha : e.columns_after_image <;>
    simp only [hb, ha, Option.map, Option.isSome, Option.getD, List.length_take, List.length_nil, ite_true,
      ite_false, Bool.false_eq_true] at h3 h4 hcap ⊢ <;>
    split_ifs at h3 h4 <;> simp_all <;> omega

end Defs
