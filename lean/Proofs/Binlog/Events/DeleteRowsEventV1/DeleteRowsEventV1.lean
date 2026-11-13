import Defs
import Proofs.Binlog.Events.RowsEvent.RowsEvent

/-! Statements for `struct DeleteRowsEventV1 and its impls` (spec file: `Specs/Binlog/Events/DeleteRowsEventV1.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.table_id e = ok e.table_id.1 := by
  rfl

/-- `num_columns`. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.num_columns e = ok e.num_columns.1 := by
  rfl

/-- `rows_data`: the raw rows. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_data
  exact binlog.events.rows_event.RowsEvent.impl.rows_data_spec e

/-- `flags`: the known flag bits. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags
  exact binlog.events.rows_event.RowsEvent.impl.flags_spec e

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags_raw e = ok e.flags.1 := by
  rfl

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_data
  step with binlog.events.rows_event.RowsEvent.impl.rows_data_spec as ⟨ s, hs ⟩
  simp [binlog.events.rows_event.RowsEventRows.new, hs]

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.into_owned
  step with binlog.events.rows_event.RowsEvent.into_owned_spec as ⟨ e1, h1 ⟩
  exact h1

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE
  exact binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq

/-- `MyDeserialize`: total; `rowsRead` with type `DELETE_ROWS_EVENT_V1` and the FDE's post-header lengths. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead .DELETE_ROWS_EVENT_V1 (postHeaderLen (fdeLens ctx.fde) .DELETE_ROWS_EVENT_V1) (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends `rowsEnc`. -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  sorry

/-- `BinlogStruct::len`: `rowsLenCrate` (see `RowsEvent::len`). -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `DELETE_ROWS_EVENT_V1` (25). -/
theorem binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .DELETE_ROWS_EVENT_V1 := by
  unfold binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
