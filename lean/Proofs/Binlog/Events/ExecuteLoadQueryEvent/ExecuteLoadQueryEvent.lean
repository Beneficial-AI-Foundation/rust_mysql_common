import Defs

/-! Statements for `struct ExecuteLoadQueryEvent and its impls` (spec file: `Specs/Binlog/Events/ExecuteLoadQueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(file_id, dup_handling, status_vars, schema)`: those fields, the lengths set (`min(len, 65535)`, `min(len, 255)`), the rest 0 or empty. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (fid : U32) (d : binlog.consts.LoadDuplicateHandling) (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new i1 i2 fid d sv sc ⦃ e => elqView e =
      { q := { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
               statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1,
               schema := cowList c2, query := [] },
        fileId := fid.val, startPos := 0, endPos := 0, dup := loadDupCode d } ⦄ := by
  sorry

/-- `thread_id`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id e = ok e.thread_id.1 := by
  sorry

/-- `execution_time`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time e = ok e.execution_time.1 := by
  sorry

/-- `error_code`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code e = ok e.error_code.1 := by
  sorry

/-- `file_id`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id e = ok e.file_id.1 := by
  sorry

/-- `start_pos`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos e = ok e.start_pos.1 := by
  sorry

/-- `end_pos`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos e = ok e.end_pos.1 := by
  sorry

/-- `dup_handling`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling e = ok e.dup_handling.1 := by
  sorry

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄ := by
  sorry

/-- `status_vars`: the status-variables block. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars e = ok e.status_vars := by
  sorry

/-- `schema_raw`: the schema, its first 255 bytes. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄ := by
  sorry

/-- `query_raw`: the query. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned e ⦃ e' => elqView e' = elqView e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; `elqRead`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs elqView (elqRead buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `elqEnc`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (elqEnc e).length ≤ Usize.max) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ elqEnc e ⦄ := by
  sorry

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = elqEnc e) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map elqView = some (elqView e) ∧ rest.val = [] ⦄ := by
  sorry

/-- `BinlogStruct::len`: the length `serialize` writes, capped, provided the status variables have at most 65522 bytes (beyond that `len` counts 65522 of them, `serialize` up to 65535). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (v : binlog.consts.BinlogVersion) (h : (cowList e.status_vars.1).length ≤ 65522) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (elqEnc e).length evLenCap ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `EXECUTE_LOAD_QUERY_EVENT` (18). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .EXECUTE_LOAD_QUERY_EVENT := by
  sorry

end mysql_common
