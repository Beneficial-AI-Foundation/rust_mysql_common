import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Binlog.Events.WriteRowsEventV1.WriteRowsEventV1
import Proofs.Binlog.Events.UpdateRowsEventV1.UpdateRowsEventV1
import Proofs.Binlog.Events.DeleteRowsEventV1.DeleteRowsEventV1
import Proofs.Binlog.Events.WriteRowsEvent.WriteRowsEvent
import Proofs.Binlog.Events.UpdateRowsEvent.UpdateRowsEvent
import Proofs.Binlog.Events.DeleteRowsEvent.DeleteRowsEvent
import Proofs.Binlog.Events.PartialUpdateRowsEvent.PartialUpdateRowsEvent

/-! Statements for `enum RowsEventData and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`: the wrapped event's. -/
theorem binlog.events.RowsEventData.table_id_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.table_id d = ok (rowsInner d).table_id.1 := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.write_rows_event_v1.WriteRowsEventV1.table_id_eq e
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.update_rows_event_v1.UpdateRowsEventV1.table_id_eq e
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.delete_rows_event_v1.DeleteRowsEventV1.table_id_eq e
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.write_rows_event.WriteRowsEvent.table_id_eq e
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.update_rows_event.UpdateRowsEvent.table_id_eq e
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.delete_rows_event.DeleteRowsEvent.table_id_eq e
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.table_id, rowsInner]
    exact binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.table_id_eq e

/-- `num_columns`: the wrapped event's. -/
theorem binlog.events.RowsEventData.num_columns_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.num_columns d = ok (rowsInner d).num_columns.1 := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.write_rows_event_v1.WriteRowsEventV1.num_columns_eq e
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.update_rows_event_v1.UpdateRowsEventV1.num_columns_eq e
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.delete_rows_event_v1.DeleteRowsEventV1.num_columns_eq e
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.write_rows_event.WriteRowsEvent.num_columns_eq e
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.update_rows_event.UpdateRowsEvent.num_columns_eq e
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.delete_rows_event.DeleteRowsEvent.num_columns_eq e
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.num_columns, rowsInner]
    exact binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.num_columns_eq e

/-- `rows_data`: the wrapped event's raw rows. -/
theorem binlog.events.RowsEventData.rows_data_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.rows_data d ⦃ s => s.val = cowList (rowsInner d).rows_data.1 ⦄ := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_data_spec e
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.update_rows_event_v1.UpdateRowsEventV1.rows_data_spec e
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_data_spec e
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.write_rows_event.WriteRowsEvent.rows_data_spec e
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.update_rows_event.UpdateRowsEvent.rows_data_spec e
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.delete_rows_event.DeleteRowsEvent.rows_data_spec e
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows_data, rowsInner]
    exact binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.rows_data_spec e

/-- `flags`: the wrapped event's known flag bits. -/
theorem binlog.events.RowsEventData.flags_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.flags d ⦃ f => f.val = (rowsInner d).flags.1.val &&& rowsEventFlagsAll ⦄ := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.write_rows_event_v1.WriteRowsEventV1.flags_spec e
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.update_rows_event_v1.UpdateRowsEventV1.flags_spec e
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.delete_rows_event_v1.DeleteRowsEventV1.flags_spec e
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.write_rows_event.WriteRowsEvent.flags_spec e
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.update_rows_event.UpdateRowsEvent.flags_spec e
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.delete_rows_event.DeleteRowsEvent.flags_spec e
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.flags, rowsInner]
    exact binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.flags_spec e

/-- `rows(tme)`: an iterator over the wrapped event's rows data, with that table map. -/
theorem binlog.events.RowsEventData.rows_spec (d : binlog.events.RowsEventData) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.RowsEventData.rows d tme ⦃ it => it.rows_event = rowsInner d ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList (rowsInner d).rows_data.1 ⦄ := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.write_rows_event_v1.WriteRowsEventV1.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.update_rows_event_v1.UpdateRowsEventV1.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.delete_rows_event_v1.DeleteRowsEventV1.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.write_rows_event.WriteRowsEvent.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.update_rows_event.UpdateRowsEvent.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.delete_rows_event.DeleteRowsEvent.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.rows, rowsInner]
    exact WP.spec_bind (binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.rows_spec e tme) (fun _ h => (WP.spec_ok _).mpr h)

/-- `into_owned`: the same variant and fields. -/
theorem binlog.events.RowsEventData.into_owned_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.into_owned d ⦃ d' => rowsVariantCode d' = rowsVariantCode d ∧ rowsView (rowsInner d') = rowsView (rowsInner d) ⦄ := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.write_rows_event_v1.WriteRowsEventV1.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.update_rows_event_v1.UpdateRowsEventV1.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.delete_rows_event_v1.DeleteRowsEventV1.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.write_rows_event.WriteRowsEvent.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.update_rows_event.UpdateRowsEvent.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.delete_rows_event.DeleteRowsEvent.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.into_owned, rowsInner, rowsVariantCode]
    exact WP.spec_bind (binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.into_owned_spec e) (fun _ h => (WP.spec_ok _).mpr ⟨rfl, h⟩)

/-- `MySerialize`: the wrapped event's layout. -/
theorem binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize_spec (d : binlog.events.RowsEventData) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc (rowsInner d)).length ≤ Usize.max) :
    binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc (rowsInner d) ⦄ := by
  cases d with
  | WriteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | UpdateRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | DeleteRowsEventV1 e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | WriteRowsEvent e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | UpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | DeleteRowsEvent e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h
  | PartialUpdateRowsEvent e =>
    simp only [binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize, rowsInner] at h ⊢
    exact binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec e buf h

end mysql_common
