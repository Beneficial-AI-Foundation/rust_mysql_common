import Proofs.Binlog.Events.ExecuteLoadQueryEvent.ExecuteLoadQueryEvent

/-!
# `src/binlog/events/execute_load_query_event.rs`
    `ExecuteLoadQueryEvent` (`EXECUTE_LOAD_QUERY_EVENT`, code 18): the query-event post-header,
    `file_id`, `start_pos`, `end_pos` (4 each), `dup_handling` (1), then status variables, schema,
    `0`, query. Covered: `new`, the field accessors, `status_vars_raw`, `schema_raw`, `query_raw`,
    `into_owned`, `SIZE`, `deserialize` (exact on any input), `serialize`, the round trip, `len`,
    `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`ElqView`, `elqView`, `elqEnc`, `elqRead`,
    `loadDupCode`, `QueryView`, `ReadsAs`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The `with_*` builders (as for `QueryEvent`: they set the field and, for status
    variables and schema, the stored length); `schema`/`query` (lossy UTF-8, excluded); the
    derived impls.

    **Behaviour to note.** The reader ignores the FDE's post-header length (unlike `QueryEvent`)
    and does not check the `0` after the schema. `len` caps the status variables at 65522 bytes
    while `serialize` writes up to 65535, so for status variables longer than 65522 bytes `len` is
    too small (the `len` statement assumes at most 65522).

    (Of these definitions, `loadDupCode` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct ExecuteLoadQueryEvent and its impls` -/

/-- `new(file_id, dup_handling, status_vars, schema)`: those fields, the lengths set (`min(len, 65535)`, `min(len, 255)`), the rest 0 or empty. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (fid : U32) (d : binlog.consts.LoadDuplicateHandling) (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new i1 i2 fid d sv sc ⦃ e => elqView e =
      { q := { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
               statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1,
               schema := cowList c2, query := [] },
        fileId := fid.val, startPos := 0, endPos := 0, dup := loadDupCode d } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new_spec`

/-- `thread_id`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id e = ok e.thread_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id_eq`

/-- `execution_time`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time e = ok e.execution_time.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time_eq`

/-- `error_code`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code e = ok e.error_code.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code_eq`

/-- `file_id`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id e = ok e.file_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id_eq`

/-- `start_pos`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos e = ok e.start_pos.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos_eq`

/-- `end_pos`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos e = ok e.end_pos.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos_eq`

/-- `dup_handling`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling e = ok e.dup_handling.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling_eq`

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw_spec`

/-- `status_vars`: the status-variables block. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars e = ok e.status_vars

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars_eq`

/-- `schema_raw`: the schema, its first 255 bytes. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw_spec`

/-- `query_raw`: the query. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw_spec`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned e ⦃ e' => elqView e' = elqView e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; `elqRead`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs elqView (elqRead buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `elqEnc`. -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (elqEnc e).length ≤ Usize.max) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ elqEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255). -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = elqEnc e) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map elqView = some (elqView e) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogStruct::len`: the length `serialize` writes, capped, provided the status variables have at most 65522 bytes (beyond that `len` counts 65522 of them, `serialize` up to 65535). -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (v : binlog.consts.BinlogVersion) (h : (cowList e.status_vars.1).length ≤ 65522) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (elqEnc e).length evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

/-- `BinlogEvent::EVENT_TYPE`: `EXECUTE_LOAD_QUERY_EVENT` (18). -/
recall binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .EXECUTE_LOAD_QUERY_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

end mysql_common
