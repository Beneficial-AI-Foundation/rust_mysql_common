import Defs
import Proofs.Binlog.Events.RowsEvent.RowsEvent

/-! Statements for `struct WriteRowsEventV1 and its impls` (spec file: `Specs/Binlog/Events/WriteRowsEventV1.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id e = ok e.table_id.1 := by
  rfl

/-- `num_columns`. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns e = ok e.num_columns.1 := by
  rfl

/-- `rows_data`: the raw rows. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data
  exact binlog.events.rows_event.RowsEvent.impl.rows_data_spec e

/-- `flags`: the known flag bits. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.flags
  exact binlog.events.rows_event.RowsEvent.impl.flags_spec e

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_raw e = ok e.flags.1 := by
  rfl

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.rows binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data
  step with binlog.events.rows_event.RowsEvent.impl.rows_data_spec as ⟨ s, hs ⟩
  simp [binlog.events.rows_event.RowsEventRows.new, hs]

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned
  step with binlog.events.rows_event.RowsEvent.into_owned_spec as ⟨ e1, h1 ⟩
  exact h1

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE
  exact binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq

/-- `MyDeserialize`: total; `rowsRead` with type `WRITE_ROWS_EVENT_V1` and the FDE's post-header lengths. `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead .WRITE_ROWS_EVENT_V1 (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT_V1) (postHeaderLen (fdeLens ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [BERUtil.rows_size_none])]
  apply WP.spec_bind (BERUtil.rows_deser_ctx h64 hsz _ buf)
  rintro ⟨r, b⟩ h
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE at h
  rcases r with v | e
  · change Aeneas.Std.WP.spec (ok (core.result.Result.Ok v, b)) _
    exact (WP.spec_ok _).mpr h
  · change Aeneas.Std.WP.spec (ok (core.result.Result.Err e, b)) _
    exact (WP.spec_ok _).mpr h

/-- `MySerialize`: appends `rowsEnc`. (64-bit target, as configured). -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize
  exact BERUtil.rows_serialize64 h64 e buf h

/-- `BinlogStruct::len`: `rowsLenCrate` (see `RowsEvent::len`). (64-bit target, as configured). -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogStruct.len
  exact BERUtil.rows_len64 h64 e v

/-- `BinlogEvent::EVENT_TYPE`: `WRITE_ROWS_EVENT_V1` (23). -/
theorem binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .WRITE_ROWS_EVENT_V1 := by
  unfold binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
