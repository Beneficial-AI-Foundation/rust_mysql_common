import Defs

/-! Statements for `enum EventData and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_owned`: the same variant (type code), and the same raw data for the uninterpreted variants. -/
theorem binlog.events.EventData.into_owned_spec (d : binlog.events.EventData) :
    binlog.events.EventData.into_owned d ⦃ d' => edTypeCode d' = edTypeCode d ∧ edRaw d' = edRaw d ∧ edUnit d' = edUnit d ⦄ := by
  sorry

/-- `MySerialize` of a data-less variant: writes nothing. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_unit (d : binlog.events.EventData) (h : edUnit d = true) (buf : alloc.vec.Vec U8) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf = ok buf := by
  sorry

/-- `MySerialize` of an uninterpreted variant: appends its raw data. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_raw (d : binlog.events.EventData) (bs : List U8) (h : edRaw d = some bs) (buf : alloc.vec.Vec U8) (hb : buf.length + bs.length ≤ Usize.max) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ bs ⦄ := by
  sorry

/-- `MySerialize` of a parsed variant: the event's own `serialize`. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_parsed (buf : alloc.vec.Vec U8) :
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.QueryEvent x) buf = binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RotateEvent x) buf = binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.IntvarEvent x) buf = binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RandEvent x) buf = binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.UserVarEvent x) buf = binlog.events.user_var_event.UserVarEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.FormatDescriptionEvent x) buf = binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.XidEvent x) buf = binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.BeginLoadQueryEvent x) buf = binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.ExecuteLoadQueryEvent x) buf = binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.TableMapEvent x) buf = binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.IncidentEvent x) buf = binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RowsQueryEvent x) buf = binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.GtidEvent x) buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.AnonymousGtidEvent x) buf = binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.PreviousGtidsEvent x) buf = binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.TransactionPayloadEvent x) buf = binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RowsEvent x) buf = binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize x buf) := by
  sorry

end mysql_common
