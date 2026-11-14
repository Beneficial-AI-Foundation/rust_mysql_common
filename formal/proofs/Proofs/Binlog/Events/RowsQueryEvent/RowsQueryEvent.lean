import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct RowsQueryEvent and its impls` (spec file: `Specs/Binlog/Events/RowsQueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(query)`: that query. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (q : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into q = ok c) :
    binlog.events.rows_query_event.RowsQueryEvent.new into q ⦃ e => cowList e.query.1 = cowList c ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.new
  step*

/-- `query_raw`: the query. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.query_raw_spec (e : binlog.events.rows_query_event.RowsQueryEvent) :
    binlog.events.rows_query_event.RowsQueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.query_raw
  step*

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.rows_query_event.RowsQueryEvent.into_owned_spec (e : binlog.events.rows_query_event.RowsQueryEvent) :
    binlog.events.rows_query_event.RowsQueryEvent.into_owned e ⦃ e' => (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) e' = (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) e ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.into_owned
  step*

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; an error on empty data, else the query is everything after the first byte. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) (if 1 ≤ buf.length then some (buf.val.drop 1, []) else none) r rest ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  all_goals
    split_ifs at r_post with hl
    · obtain ⟨⟨_, rfl⟩, hb1⟩ := r_post
      simp_all [ReadsAs, okPart]
    · obtain ⟨_, rfl⟩ := r_post
      simp_all [ReadsAs, okPart]

/-- `MySerialize`: appends the layout `rowsQueryEnc`. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rows_query_event.RowsQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (rowsQueryEnc e).length ≤ Usize.max) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsQueryEnc e ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [rowsQueryEnc, List.length_cons] at h
  step*
  · simp_all [rowsQueryEnc, List.replicate_one]

/-- Round trip. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rows_query_event.RowsQueryEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = rowsQueryEnc e) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.rows_query_event.RowsQueryEvent) => cowList x.query.1) = some (cowList e.query.1) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  have hl : 1 ≤ buf.length := by simp [Slice.length, h, rowsQueryEnc]
  simp only [hl, ite_true, h, rowsQueryEnc, List.drop_succ_cons, List.drop_zero] at hr
  exact hr

/-- `BinlogEvent::EVENT_TYPE`: `ROWS_QUERY_EVENT` (29). -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ROWS_QUERY_EVENT := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: the length of what `serialize` writes (`rowsQueryEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rows_query_event.RowsQueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (rowsQueryEnc e).length evLenCap ⦄ := by
  unfold binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  obtain ⟨p, c, u⟩ := e
  simp only
  step*
  · rw [i1_post]; simp [BinlogEvGtid.header_len_val]
  · have := BinlogEvGtid.u32_max_le_usize
    have hs : s.len.val = (cowList c).length := by simp [s_post]
    have hh := BinlogEvGtid.header_len_val
    simp only [n_post, len1_post, i2_post, i1_post, len_post, hh, hs,
      rowsQueryEnc, List.length_cons, evLenCap]
    rw [BinlogEvGtid.min_usize_cap, BinlogEvGtid.min_one_usize, Nat.add_comm]

end mysql_common
