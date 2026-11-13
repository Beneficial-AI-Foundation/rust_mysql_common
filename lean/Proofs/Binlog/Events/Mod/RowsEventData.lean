import Defs

/-! Statements for `enum RowsEventData and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`: the wrapped event's. -/
theorem binlog.events.RowsEventData.table_id_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.table_id d = ok (rowsInner d).table_id.1 := by
  sorry

/-- `num_columns`: the wrapped event's. -/
theorem binlog.events.RowsEventData.num_columns_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.num_columns d = ok (rowsInner d).num_columns.1 := by
  sorry

/-- `rows_data`: the wrapped event's raw rows. -/
theorem binlog.events.RowsEventData.rows_data_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.rows_data d ⦃ s => s.val = cowList (rowsInner d).rows_data.1 ⦄ := by
  sorry

/-- `flags`: the wrapped event's known flag bits. -/
theorem binlog.events.RowsEventData.flags_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.flags d ⦃ f => f.val = (rowsInner d).flags.1.val &&& rowsEventFlagsAll ⦄ := by
  sorry

/-- `rows(tme)`: an iterator over the wrapped event's rows data, with that table map. -/
theorem binlog.events.RowsEventData.rows_spec (d : binlog.events.RowsEventData) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.RowsEventData.rows d tme ⦃ it => it.rows_event = rowsInner d ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList (rowsInner d).rows_data.1 ⦄ := by
  sorry

/-- `into_owned`: the same variant and fields. -/
theorem binlog.events.RowsEventData.into_owned_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.into_owned d ⦃ d' => rowsVariantCode d' = rowsVariantCode d ∧ rowsView (rowsInner d') = rowsView (rowsInner d) ⦄ := by
  sorry

/-- `MySerialize`: the wrapped event's layout. -/
theorem binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize_spec (d : binlog.events.RowsEventData) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc (rowsInner d)).length ≤ Usize.max) :
    binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc (rowsInner d) ⦄ := by
  sorry

end mysql_common
