import Proofs.Binlog.Events.QueryEvent.QueryEvent
import Proofs.Binlog.Events.QueryEvent.StatusVar
import Proofs.Binlog.Events.QueryEvent.StatusVars
import Proofs.Binlog.Events.QueryEvent.StatusVarsIterator

/-!
# `src/binlog/events/query_event.rs`
    `QueryEvent` (`QUERY_EVENT`, code 2) and its status variables (`StatusVars`,
    `StatusVarsIterator`, `StatusVar::get_value`). Covered: `new`, the `with_*` builders, every
    accessor, `into_owned`, `SIZE`, `deserialize` (exact on any input, with the FDE's post-header
    length), `serialize`, the round trip, `len`, `EVENT_TYPE`; `StatusVars::deserialize`,
    `serialize`, `iter`, `get_status_var`; the iterator's `next` (exact: the walk `statusVarsOf`);
    `get_value` (exact per key, against the format's decoding `svValRead`, with the two bugs
    below stated separately).

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155, in
    particular 146: status variable values read with `ParseBuf`, 147: the iterator's helpers as
    functions, recursions instead of loops (stack proportional to the number of names / status
    variables)). **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the
    stack is not modelled. When a reader fails, what it leaves of the buffer is not stated.

    **Definitions used.** `Defs/BinlogEvents.lean` (`QueryView`, `queryView`, `queryEnc`,
    `queryRead`, `postHeaderLen`, `fdeLens`, `svKeyCode`, `svKeyOfCode`, `svValueLen`,
    `dbNamesLen`, `svWalk`, `statusVarsOf`, `svStep`, `SvView`, `svValView`, `svValRead`, `lp1`,
    `dbNames`, `dbNamesCrate`, `ReadsAs`, `takeExact`, `evLenCap`), `Defs/Connection.lean`
    (`hasNul`, `NoNul`), `Defs/Bytes.lean`. **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `schema` and `query` (lossy UTF-8, excluded); the `Debug` impls (they iterate
    and format); `Clone`/`PartialEq`/`Hash` (derived; those of `StatusVarVal` excluded).

    **Behaviour to note (bugs first).**
    * **`Q_UPDATED_DB_NAMES`: every name after the first is read as empty** (`updated_db_names`
      recurses on `&read[index..]`, which still starts with the `0` terminator):
      `get_value_updated_db_names` gives `dbNamesCrate`, not the format's `dbNames`. The
      iterator's length computation is right, so only the decoded value is wrong.
    * **`Q_MICROSECONDS` never decodes:** the iterator slices it as 3 bytes (as MySQL writes it)
      but `get_value` reads a `u32` from it, so it is always an error
      (`get_value_microseconds_bug`).
    * The count 254 of `Q_UPDATED_DB_NAMES` (`OVER_MAX_DBS_IN_EVENT_MTS`: no names follow) is read
      as 254 names (`svValueLen`).
    * The reader skips the byte after the schema without checking it is `0`. `serialize` writes
      the stored `schema_len` / `status_vars_len` (kept consistent by `new` / `with_*`) and 13
      post-header bytes, so the round trip needs an FDE whose query post-header is at most 13.
    * The iterator stops silently (no error) at an unknown key or a truncated value.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct QueryEvent and its impls` -/

/-- `new(status_vars, schema)`: those, with their lengths (`min(len, 65535)`, `min(len, 255)`), everything else 0 or empty. -/
recall binlog.events.query_event.QueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.query_event.QueryEvent.new i1 i2 sv sc ⦃ e => queryView e =
      { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
        statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1, schema := cowList c2, query := [] } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.new_spec`

/-- `with_thread_id`. -/
recall binlog.events.query_event.QueryEvent.with_thread_id_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_thread_id e x ⦃ e' => queryView e' = { queryView e with threadId := x.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_thread_id_spec`

/-- `with_execution_time`. -/
recall binlog.events.query_event.QueryEvent.with_execution_time_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_execution_time e x ⦃ e' => queryView e' = { queryView e with execTime := x.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_execution_time_spec`

/-- `with_error_code`. -/
recall binlog.events.query_event.QueryEvent.with_error_code_spec (e : binlog.events.query_event.QueryEvent) (x : U16) :
    binlog.events.query_event.QueryEvent.with_error_code e x ⦃ e' => queryView e' = { queryView e with errorCode := x.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_error_code_spec`

/-- `with_status_vars`: the status variables and their length. -/
recall binlog.events.query_event.QueryEvent.with_status_vars_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.query_event.QueryEvent.with_status_vars into e sv ⦃ e' => queryView e' = { queryView e with statusVars := cowList c, statusVarsLen := min (cowList c).length 65535 } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_status_vars_spec`

/-- `with_schema`: the schema and its length. -/
recall binlog.events.query_event.QueryEvent.with_schema_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sc : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sc = ok c) :
    binlog.events.query_event.QueryEvent.with_schema into e sc ⦃ e' => queryView e' = { queryView e with schema := cowList c, schemaLen := min (cowList c).length 255 } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_schema_spec`

/-- `with_query`. -/
recall binlog.events.query_event.QueryEvent.with_query_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (q : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into q = ok c) :
    binlog.events.query_event.QueryEvent.with_query into e q ⦃ e' => queryView e' = { queryView e with query := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.with_query_spec`

/-- `thread_id`. -/
recall binlog.events.query_event.QueryEvent.impl.thread_id_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.thread_id e = ok e.thread_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.impl.thread_id_eq`

/-- `execution_time`. -/
recall binlog.events.query_event.QueryEvent.impl.execution_time_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.execution_time e = ok e.execution_time.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.impl.execution_time_eq`

/-- `error_code`. -/
recall binlog.events.query_event.QueryEvent.impl.error_code_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.error_code e = ok e.error_code.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.impl.error_code_eq`

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
recall binlog.events.query_event.QueryEvent.status_vars_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.status_vars_raw_spec`

/-- `status_vars`: the status-variables block. -/
recall binlog.events.query_event.QueryEvent.impl.status_vars_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.status_vars e = ok e.status_vars

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.impl.status_vars_eq`

/-- `schema_raw`: the schema, its first 255 bytes. -/
recall binlog.events.query_event.QueryEvent.schema_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.schema_raw_spec`

/-- `query_raw`: the query. -/
recall binlog.events.query_event.QueryEvent.query_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.query_raw_spec`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.query_event.QueryEvent.into_owned_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.into_owned e ⦃ e' => queryView e' = queryView e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; `queryRead` with the FDE's query post-header length. -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs queryView (queryRead (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT) buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `queryEnc`. -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.query_event.QueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (queryEnc e).length ≤ Usize.max) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ queryEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255), read with a query post-header of at most 13 bytes (`serialize` writes 13). -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.query_event.QueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT ≤ 13)
    (buf : io.ParseBuf) (h : buf.val = queryEnc e) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map queryView = some (queryView e) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `QUERY_EVENT` (2). -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .QUERY_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: the length of what `serialize` writes (`queryEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.query_event.QueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (queryEnc e).length evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

/-! ### `struct StatusVar and its impls` -/

/-- `get_value`: the value decoded per its key (`svValRead`); the raw value as the error if it is too short. (`Q_UPDATED_DB_NAMES` and `Q_MICROSECONDS`: see below.) -/
recall binlog.events.query_event.StatusVar.get_value_spec (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key ≠ 12 ∧ svKeyCode v.key ≠ 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match r with
      | .Ok x => svValRead (svKeyCode v.key) v.value.val = some (svValView x)
      | .Err e => svValRead (svKeyCode v.key) v.value.val = none ∧ e = v.value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVar.get_value_spec`

/-- **Upstream bug:** `get_value` of `Q_UPDATED_DB_NAMES` gives `dbNamesCrate` (the first name, then empty names), not the names of the format (`dbNames`); the raw value as the error without a count or a terminated first name. -/
recall binlog.events.query_event.StatusVar.get_value_updated_db_names (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 12) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match v.value.val with
      | [] => r = .Err v.value
      | c :: rest => match dbNamesCrate c.val rest with
        | some ns => ∃ x, r = .Ok x ∧ svValView x = (12, [], ns)
        | none => r = .Err v.value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVar.get_value_updated_db_names`

/-- `get_value` of `Q_MICROSECONDS` reads a 4-byte integer (the format has 3). -/
recall binlog.events.query_event.StatusVar.get_value_microseconds (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => if 4 ≤ v.value.length then ∃ x, r = .Ok x ∧ svValView x = (13, [leNat (v.value.val.take 4)], [])
      else r = .Err v.value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVar.get_value_microseconds`

/-- **Upstream bug:** every `Q_MICROSECONDS` variable the iterator yields (3 bytes) fails to decode. -/
recall binlog.events.query_event.StatusVar.get_value_microseconds_bug (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 13) (hl : v.value.length = 3) :
    binlog.events.query_event.StatusVar.get_value v = ok (.Err v.value)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVar.get_value_microseconds_bug`

/-! ### `struct StatusVars and its impls` -/

/-- `iter`: an iterator at position 0 over the block (its first 65535 bytes). -/
recall binlog.events.query_event.StatusVars.iter_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.iter s ⦃ it => it.pos.val = 0 ∧ it.status_vars.val = (cowList s.1).take 65535 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVars.iter_spec`

/-- `get_status_var(key)`: the first variable with that key in the walk, if any. -/
recall binlog.events.query_event.StatusVars.get_status_var_spec (s : binlog.events.query_event.StatusVars) (k : binlog.consts.StatusVarKey) :
    binlog.events.query_event.StatusVars.get_status_var s k ⦃ o => o.map (fun x => (svKeyCode x.key, x.value.val)) =
      (statusVarsOf ((cowList s.1).take 65535)).find? (fun kv => kv.1 = svKeyCode k) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVars.get_status_var_spec`

/-- `into_owned`: the same bytes. -/
recall binlog.events.query_event.StatusVars.into_owned_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.into_owned s ⦃ s' => cowList s'.1 = cowList s.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVars.into_owned_spec`

/-- `MyDeserialize` with the length `len`: total; that many bytes, an error with the buffer unchanged if fewer. -/
recall binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec (len : U16) (buf : io.ParseBuf) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec`

/-- `MySerialize`: the bytes, truncated to 65535. -/
recall binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec (s : binlog.events.query_event.StatusVars) (buf : alloc.vec.Vec U8) (h : buf.length + min (cowList s.1).length 65535 ≤ Usize.max) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize s buf ⦃ buf' => buf'.val = buf.val ++ (cowList s.1).take 65535 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct StatusVarsIterator and its impls` -/

/-- `new(bytes)`: at position 0. -/
recall binlog.events.query_event.StatusVarsIterator.new_spec (s : Slice U8) :
    binlog.events.query_event.StatusVarsIterator.new s = ok { pos := 0#usize, status_vars := s }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVarsIterator.new_spec`

/-- `Iterator::next`: the next variable of the walk from the current position (`svStep`), and the position after it; `None` at an unknown key, a truncated value, or the end. -/
recall binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next_spec (it : binlog.events.query_event.StatusVarsIterator) (h : it.pos.val ≤ it.status_vars.length) :
    binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next it ⦃ o it' =>
      match svStep it.status_vars.val it.pos.val with
      | some (kv, p) => o.map (fun x => (svKeyCode x.key, x.value.val)) = some kv ∧ it'.pos.val = p ∧ it'.status_vars = it.status_vars
      | none => o = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next_spec`

end mysql_common
