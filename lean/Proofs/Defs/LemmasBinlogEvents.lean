import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr

/-! Facts about the binlog-event definitions (`lean/Defs/BinlogEvents.lean`) (spec file:
`Specs/DefsBinlogEvents.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common mysql_common.EvHdrUtil

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
  have hA := PBUtil.length_leBytes 2 (binlogVersionCode e.binlog_version.1)
  have hB := fixedText_length 50 (cowList e.server_version.1)
  have hC := PBUtil.length_leBytes 4 e.create_timestamp.1.val
  have hv : binlogVersionCode e.binlog_version.1 < 2 ^ 16 := by cases e.binlog_version.1 <;> simp [binlogVersionCode]
  have hts : e.create_timestamp.1.val < 2 ^ 32 := by scalar_tac
  have hvc : binlogVersionOfCode (binlogVersionCode e.binlog_version.1) = some e.binlog_version.1 := by
    cases e.binlog_version.1 <;> rfl
  unfold fdeRead fdeEnc
  have hlen : ¬ (leBytes 2 (binlogVersionCode e.binlog_version.1) ++ fixedText 50 (cowList e.server_version.1) ++
      leBytes 4 e.create_timestamp.1.val ++ [byte 19] ++ fdeLens e).length < 57 := by
    simp only [List.length_append, hA, hB, hC, List.length_cons, List.length_nil]; omega
  simp only [hlen, ite_false]
  simp only [List.append_assoc]
  rw [List.take_left' hA, mysql_common.EvHdrUtil.leNat_leBytes_lt 2 _ hv, hvc]
  have e56 : (leBytes 2 (binlogVersionCode e.binlog_version.1) ++ (fixedText 50 (cowList e.server_version.1) ++
      (leBytes 4 e.create_timestamp.1.val ++ ([byte 19] ++ fdeLens e))))[56]? = some (byte 19) := by
    rw [List.getElem?_append_right (by omega), hA, List.getElem?_append_right (by omega), hB,
      List.getElem?_append_right (by omega), hC]
    rfl
  simp only [e56, Option.map_some]
  simp only [show (byte 19).val = 19 from rfl, ne_eq, not_true_eq_false, ite_false]
  simp only [List.drop_left' hA]
  rw [List.take_left' hB]
  have d52 : List.drop 52 (leBytes 2 (binlogVersionCode e.binlog_version.1) ++ (fixedText 50 (cowList e.server_version.1) ++
      (leBytes 4 e.create_timestamp.1.val ++ ([byte 19] ++ fdeLens e)))) =
      leBytes 4 e.create_timestamp.1.val ++ ([byte 19] ++ fdeLens e) := by
    rw [show 52 = 2 + 50 from rfl, ← List.drop_drop, List.drop_left' hA, List.drop_left' hB]
  have d57 : List.drop 57 (leBytes 2 (binlogVersionCode e.binlog_version.1) ++ (fixedText 50 (cowList e.server_version.1) ++
      (leBytes 4 e.create_timestamp.1.val ++ ([byte 19] ++ fdeLens e)))) = fdeLens e := by
    rw [show 57 = 52 + 4 + 1 from rfl, ← List.drop_drop, ← List.drop_drop, d52, List.drop_left' hC]; rfl
  rw [d52, d57, List.take_left' hC, mysql_common.EvHdrUtil.leNat_leBytes_lt 4 _ hts]
  rfl

/-- The query reader inverts the encoder, for consistent lengths and a post-header of at most 13 bytes. -/
theorem queryRead_queryEnc (e : binlog.events.query_event.QueryEvent) (p : Nat) (hp : p ≤ 13)
    (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length) (hsv' : (cowList e.status_vars.1).length ≤ 65535)
    (hs : e.schema_len.1.val = (cowList e.schema.1).length) (hs' : (cowList e.schema.1).length ≤ 255) :
    queryRead p (queryEnc e) = some (queryView e, []) := by
  have hsvt : (cowList e.status_vars.1).take 65535 = cowList e.status_vars.1 := List.take_of_length_le hsv'
  have hsct : (cowList e.schema.1).take 255 = cowList e.schema.1 := List.take_of_length_le hs'
  have a1 := PBUtil.length_leBytes 4 e.thread_id.1.val
  have a2 := PBUtil.length_leBytes 4 e.execution_time.1.val
  have a3 := PBUtil.length_leBytes 2 e.error_code.1.val
  have a4 := PBUtil.length_leBytes 2 e.status_vars_len.1.val
  have b1 : e.thread_id.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b2 : e.execution_time.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b3 : e.error_code.1.val < 2 ^ (8 * 2) := by scalar_tac
  have b4 : e.status_vars_len.1.val < 2 ^ (8 * 2) := by scalar_tac
  set H := leBytes 4 e.thread_id.1.val ++ leBytes 4 e.execution_time.1.val ++ [e.schema_len.1] ++
    leBytes 2 e.error_code.1.val ++ leBytes 2 e.status_vars_len.1.val with hH
  have hHl : H.length = 13 := by simp [hH, a1, a2, a3, a4]
  have hq : queryEnc e = H ++ (cowList e.status_vars.1 ++ (cowList e.schema.1 ++ ([byte 0] ++ cowList e.query.1))) := by
    simp only [queryEnc, hsvt, hsct, hH, List.append_assoc]
  have t4 : H.take 4 = leBytes 4 e.thread_id.1.val := by simp [hH, a1]
  have t44 : (H.drop 4).take 4 = leBytes 4 e.execution_time.1.val := by simp [hH, a1, a2]
  have t8 : (H.drop 8).headD (byte 0) = e.schema_len.1 := by simp [hH, List.drop_append, a1, a2]
  have t92 : (H.drop 9).take 2 = leBytes 2 e.error_code.1.val := by simp [hH, List.drop_append, a1, a2, a3]
  have t112 : (H.drop 11).take 2 = leBytes 2 e.status_vars_len.1.val := by simp [hH, List.drop_append, a1, a2, a3, a4]
  have hp0 : p - 13 = 0 := by omega
  rw [hq]
  simp only [queryRead, Option.bind_eq_bind]
  rw [takeExact_app _ _ 13 hHl]
  simp only [Option.bind_some, hp0, t112, t8, t4, t44, t92]
  have z : ∀ l : List U8, takeExact 0 l = some ([], l) := fun l => by simp [takeExact]
  simp only [z, Option.bind_some, leNat_leBytes_lt 2 _ b4, leNat_leBytes_lt 2 _ b3, leNat_leBytes_lt 4 _ b1,
    leNat_leBytes_lt 4 _ b2]
  rw [hsv, takeExact_app _ _ _ rfl]
  simp only [Option.bind_some]
  rw [hs, takeExact_app _ _ _ rfl]
  simp only [Option.bind_some]
  rw [takeExact_app [byte 0] _ 1 rfl]
  simp only [Option.bind_some, queryView, hsv, hs]

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
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hf : e.flags.1.val < 2 ^ (8 * 2) := by scalar_tac
  have ht' : e.table_id.1.val < 2 ^ (8 * 6) := by simpa using ht
  have hn : e.columns_count.1.val < 2 ^ 64 := by scalar_tac
  have hm : (cowList e.columns_metadata.1).length < 2 ^ 64 :=
    mysql_common.lt_two_pow_64_of_le_max (PKUtil.cowList_length_le _)
  have hb : (cowList e.null_bitmask.1).take (2 ^ 61) = cowList e.null_bitmask.1 := by
    apply List.take_of_length_le; rw [h4]; omega
  have r6 : ∀ R, readLE 6 (leBytes 6 e.table_id.1.val ++ R) = some (e.table_id.1.val, R) := fun R => readLE_app 6 _ R ht'
  have r2 : ∀ R, readLE 2 (leBytes 2 e.flags.1.val ++ R) = some (e.flags.1.val, R) := fun R => readLE_app 2 _ R hf
  have c1 : ∀ R, checkedLenPrefixed 1 (u8Str (cowList e.database_name.1) ++ R) = (some (cowList e.database_name.1), R) :=
    fun R => clp_u8Str _ R h1
  have c2 : ∀ R, checkedLenPrefixed 1 (u8Str (cowList e.table_name.1) ++ R) = (some (cowList e.table_name.1), R) :=
    fun R => clp_u8Str _ R h2
  have c3 : ∀ R, checkedLenencInt (lenencInt e.columns_count.1.val ++ R) = (some e.columns_count.1.val, R) :=
    fun R => PBUtil.checkedLenencInt_lenencInt _ R hn
  have c4 : ∀ R, checkedLenencStr (lenencStr (cowList e.columns_metadata.1) ++ R) = (some (cowList e.columns_metadata.1), R) :=
    fun R => cls_lenencStr _ R hm
  have t1 : ∀ R, takeExact 1 ([byte 0] ++ R) = some ([byte 0], R) := fun R => takeExact_app _ R 1 rfl
  have tn : ∀ R, takeExact e.columns_count.1.val (cowList e.columns_type.1 ++ R) = some (cowList e.columns_type.1, R) :=
    fun R => takeExact_app _ R _ h3
  have tb : ∀ R, takeExact ((e.columns_count.1.val + 7) / 8) (cowList e.null_bitmask.1 ++ R) = some (cowList e.null_bitmask.1, R) :=
    fun R => takeExact_app _ R _ h4
  simp only [tmRead, tmEnc, hp, ite_false, Option.bind_eq_bind, List.append_assoc, r6, Option.bind_some, r2, c1, optFst,
    t1, c2, c3, tn, c4, hb, tb, tmView]

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
