import Defs

/-! Statements for `struct RowsEvent and its impls` (spec file: `Specs/Binlog/Events/RowsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `event_type`. -/
theorem binlog.events.rows_event.RowsEvent.impl.event_type_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.event_type e = ok e.event_type := by
  sorry

/-- `table_id`. -/
theorem binlog.events.rows_event.RowsEvent.impl.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.table_id e = ok e.table_id.1 := by
  sorry

/-- `num_columns`. -/
theorem binlog.events.rows_event.RowsEvent.impl.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.num_columns e = ok e.num_columns.1 := by
  sorry

/-- `rows_data`: the raw rows. -/
theorem binlog.events.rows_event.RowsEvent.impl.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  sorry

/-- `flags`: the known flag bits. -/
theorem binlog.events.rows_event.RowsEvent.impl.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  sorry

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.rows_event.RowsEvent.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.flags_raw e = ok e.flags.1 := by
  sorry

/-- `len`: `rowsLenCrate`. -/
theorem binlog.events.rows_event.RowsEvent.len_spec (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  sorry

/-- `len` of a consistent v2 event: the length `serialize` writes, capped. -/
theorem binlog.events.rows_event.RowsEvent.len_v2 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h2 : rowsIsV2 e.event_type = true) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = min (rowsEnc e).length evLenCap ⦄ := by
  sorry

/-- **Quirk:** `len` of a consistent v1 event is 2 more than the length `serialize` writes (when under the cap). -/
theorem binlog.events.rows_event.RowsEvent.len_v1 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false) (v : binlog.consts.BinlogVersion)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = (rowsEnc e).length + 2 ⦄ := by
  sorry

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.rows_event.RowsEvent.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.rows_event.RowsEvent.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.rows_event.RowsEvent.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE = none := by
  sorry

/-- `MyDeserialize` with the context's event type and FDE: total; `rowsRead`. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize_spec (h64 : Target64) (ctx : binlog.events.rows_event.RowsEventCtx) (buf : io.ParseBuf) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead ctx.event_type (postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type) (postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends `rowsEnc`. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  sorry

/-- Round trip, for a consistent event of the context's type with a table id below `2^48`, read with an FDE whose post-header lengths agree with the type (6 bytes excluded; equal to `WRITE_ROWS_EVENT`'s iff v2). -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.roundtrip (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.events.rows_event.RowsEventCtx) (he : eventTypeCode ctx.event_type = eventTypeCode e.event_type)
    (hp : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type ≠ 6) (hv : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type = postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT ↔ rowsIsV2 e.event_type = true)
    (buf : io.ParseBuf) (h : buf.val = rowsEnc e) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => (okPart r).map rowsView = some (rowsView e) ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
