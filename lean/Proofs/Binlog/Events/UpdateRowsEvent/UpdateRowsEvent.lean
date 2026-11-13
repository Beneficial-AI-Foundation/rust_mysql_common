import Defs

/-! Statements for `struct UpdateRowsEvent and its impls` (spec file: `Specs/Binlog/Events/UpdateRowsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.table_id e = ok e.table_id.1 := by
  sorry

/-- `num_columns`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.num_columns e = ok e.num_columns.1 := by
  sorry

/-- `rows_data`: the raw rows. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  sorry

/-- `flags`: the known flag bits. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  sorry

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.flags_raw e = ok e.flags.1 := by
  sorry

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; `rowsRead` with type `UPDATE_ROWS_EVENT` and the FDE's post-header lengths. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead .UPDATE_ROWS_EVENT (postHeaderLen (fdeLens ctx.fde) .UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends `rowsEnc`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  sorry

/-- `BinlogStruct::len`: `rowsLenCrate` (see `RowsEvent::len`). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `UPDATE_ROWS_EVENT` (31). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .UPDATE_ROWS_EVENT := by
  sorry

end mysql_common
