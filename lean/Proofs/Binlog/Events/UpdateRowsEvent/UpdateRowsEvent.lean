import Defs
import Proofs.Binlog.Events.RowsEvent.RowsEvent

/-! Statements for `struct UpdateRowsEvent and its impls` (spec file: `Specs/Binlog/Events/UpdateRowsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.table_id e = ok e.table_id.1 := by
  rfl

/-- `num_columns`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.num_columns e = ok e.num_columns.1 := by
  rfl

/-- `rows_data`: the raw rows. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.rows_data
  exact binlog.events.rows_event.RowsEvent.impl.rows_data_spec e

/-- `flags`: the known flag bits. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.flags
  exact binlog.events.rows_event.RowsEvent.impl.flags_spec e

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.flags_raw e = ok e.flags.1 := by
  rfl

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.rows binlog.events.update_rows_event.UpdateRowsEvent.rows_data
  step with binlog.events.rows_event.RowsEvent.impl.rows_data_spec as ⟨ s, hs ⟩
  simp [binlog.events.rows_event.RowsEventRows.new, hs]

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.update_rows_event.UpdateRowsEvent.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.into_owned
  step with binlog.events.rows_event.RowsEvent.into_owned_spec as ⟨ e1, h1 ⟩
  exact h1

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE
  exact binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq

/-- `MyDeserialize`: total; `rowsRead` with type `UPDATE_ROWS_EVENT` and the FDE's post-header lengths. `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead .UPDATE_ROWS_EVENT (postHeaderLen (fdeLens ctx.fde) .UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends `rowsEnc`. (64-bit target, as configured). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize
  exact BERUtil.rows_serialize64 h64 e buf h

/-- `BinlogStruct::len`: `rowsLenCrate` (see `RowsEvent::len`). (64-bit target, as configured). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  exact BERUtil.rows_len64 h64 e v

/-- `BinlogEvent::EVENT_TYPE`: `UPDATE_ROWS_EVENT` (31). -/
theorem binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .UPDATE_ROWS_EVENT := by
  unfold binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
