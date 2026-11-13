import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Defs.LemmasBinlogEvents

/-! Statements for `struct QueryEvent and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `new(status_vars, schema)`: those, with their lengths (`min(len, 65535)`, `min(len, 255)`), everything else 0 or empty. -/
theorem binlog.events.query_event.QueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.query_event.QueryEvent.new i1 i2 sv sc ⦃ e => queryView e =
      { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
        statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1, schema := cowList c2, query := [] } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.new
  step with PKUtil.rawbytes_new_spec _ i1 sv c1 h1 as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_new_spec _ i2 sc c2 h2 as ⟨rb2, hrb2⟩
  step*
  have e1 : (UScalar.cast .U8 i).val = min (cowList c2).length 255 := by
    rw [cast_u8_small i (by omega), i_post, hrb2]
  have e3 : (UScalar.cast .U16 i2).val = min (cowList c1).length 65535 := by
    rw [cast_u16_small i2 (by omega), i2_post, hrb]
  simp_all [queryView]

/-- `with_thread_id`. -/
theorem binlog.events.query_event.QueryEvent.with_thread_id_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_thread_id e x ⦃ e' => queryView e' = { queryView e with threadId := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_thread_id
  step*
  simp_all [queryView]

/-- `with_execution_time`. -/
theorem binlog.events.query_event.QueryEvent.with_execution_time_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_execution_time e x ⦃ e' => queryView e' = { queryView e with execTime := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_execution_time
  step*
  simp_all [queryView]

/-- `with_error_code`. -/
theorem binlog.events.query_event.QueryEvent.with_error_code_spec (e : binlog.events.query_event.QueryEvent) (x : U16) :
    binlog.events.query_event.QueryEvent.with_error_code e x ⦃ e' => queryView e' = { queryView e with errorCode := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_error_code
  step*
  simp_all [queryView]

/-- `with_status_vars`: the status variables and their length. -/
theorem binlog.events.query_event.QueryEvent.with_status_vars_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.query_event.QueryEvent.with_status_vars into e sv ⦃ e' => queryView e' = { queryView e with statusVars := cowList c, statusVarsLen := min (cowList c).length 65535 } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_status_vars
  obtain ⟨a, b, c0, d, ⟨x, pd⟩, sv0, sc0, sk, q0⟩ := e
  step with PKUtil.rawbytes_new_spec _ into sv c h as ⟨rb, hrb⟩
  step with bare_len_spec as ⟨i, hi⟩
  simp only [lift, bind_ok]
  apply (WP.spec_ok _).mpr
  rw [hrb] at hi
  simp [queryView, hrb, cast_u16_small i (by omega), hi]

/-- `with_schema`: the schema and its length. -/
theorem binlog.events.query_event.QueryEvent.with_schema_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sc : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sc = ok c) :
    binlog.events.query_event.QueryEvent.with_schema into e sc ⦃ e' => queryView e' = { queryView e with schema := cowList c, schemaLen := min (cowList c).length 255 } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_schema
  obtain ⟨a, b, ⟨x, pd⟩, d, f, sv0, sc0, sk, q0⟩ := e
  step with PKUtil.rawbytes_new_spec _ into sc c h as ⟨rb, hrb⟩
  step with bare_len_spec as ⟨i, hi⟩
  simp only [lift, bind_ok]
  apply (WP.spec_ok _).mpr
  rw [hrb] at hi
  simp [queryView, hrb, cast_u8_small i (by omega), hi]

/-- `with_query`. -/
theorem binlog.events.query_event.QueryEvent.with_query_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (q : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into q = ok c) :
    binlog.events.query_event.QueryEvent.with_query into e q ⦃ e' => queryView e' = { queryView e with query := cowList c } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_query
  step with PKUtil.rawbytes_new_spec _ into q c h as ⟨rb, hrb⟩
  simp [queryView, hrb]

/-- `thread_id`. -/
theorem binlog.events.query_event.QueryEvent.impl.thread_id_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.thread_id e = ok e.thread_id.1 := by
  obtain ⟨⟨_, _⟩, _⟩ := e; rfl

/-- `execution_time`. -/
theorem binlog.events.query_event.QueryEvent.impl.execution_time_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.execution_time e = ok e.execution_time.1 := by
  obtain ⟨_, ⟨_, _⟩, _⟩ := e; rfl

/-- `error_code`. -/
theorem binlog.events.query_event.QueryEvent.impl.error_code_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.error_code e = ok e.error_code.1 := by
  obtain ⟨_, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
theorem binlog.events.query_event.QueryEvent.status_vars_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.status_vars_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 65535#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `status_vars`: the status-variables block. -/
theorem binlog.events.query_event.QueryEvent.impl.status_vars_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.status_vars e = ok e.status_vars := by
  rfl

/-- `schema_raw`: the schema, its first 255 bytes. -/
theorem binlog.events.query_event.QueryEvent.schema_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.schema_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 255#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `query_raw`: the query. -/
theorem binlog.events.query_event.QueryEvent.query_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.query_raw
  exact PKUtil.eof_as_bytes_spec _

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.query_event.QueryEvent.into_owned_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.into_owned e ⦃ e' => queryView e' = queryView e ⦄ := by
  unfold binlog.events.query_event.QueryEvent.into_owned binlog.events.query_event.StatusVars.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb1, hrb1⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb2, hrb2⟩
  simp [hrb, hrb1, hrb2, queryView]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `queryRead` with the FDE's query post-header length. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs queryView (queryRead (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `queryEnc`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.query_event.QueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (queryEnc e).length ≤ Usize.max) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ queryEnc e ⦄ := by
  sorry

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255), read with a query post-header of at most 13 bytes (`serialize` writes 13). -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.query_event.QueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT ≤ 13)
    (buf : io.ParseBuf) (h : buf.val = queryEnc e) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map queryView = some (queryView e) ∧ rest.val = [] ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `QUERY_EVENT` (2). -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .QUERY_EVENT := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: the length of what `serialize` writes (`queryEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.query_event.QueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (queryEnc e).length evLenCap ⦄ := by
  sorry

end mysql_common
