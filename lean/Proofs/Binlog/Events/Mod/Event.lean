import Defs

/-! Statements for `struct Event and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `fde`: the format description event the event was read with. -/
theorem binlog.events.Event.impl.fde_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.fde self = ok self.fde := by
  sorry

/-- `header`: the common header. -/
theorem binlog.events.Event.impl.header_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.header self = ok self.header := by
  sorry

/-- `data`: the event data (footer stripped). -/
theorem binlog.events.Event.impl.data_spec (self : binlog.events.Event) :
    binlog.events.Event.impl.data self ⦃ s => s.val = self.data.val ⦄ := by
  sorry

/-- `footer`. -/
theorem binlog.events.Event.impl.footer_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.footer self = ok self.footer := by
  sorry

/-- `checksum`: the stored checksum iff the event carries one (`evHasChecksum`). -/
theorem binlog.events.Event.impl.checksum_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.checksum self = ok (if evHasChecksum self.footer self.header.event_type.1.val then some self.checksum else none) := by
  sorry

/-- `len` (private, used by `write`): `eventLen`. -/
theorem binlog.events.Event.len_spec (self : binlog.events.Event) (v : binlog.consts.BinlogVersion) :
    binlog.events.Event.len self v ⦃ n => n.val = eventLen self ⦄ := by
  sorry

/-- `read_event::<T>`: `T` is parsed from the data with `parse` (so `T::SIZE` is checked) in the context (`19 + data.len()`, the FDE, the raw type); its error is passed on; a success is `Ok` iff no bytes are left, and otherwise the (opaque) `bytes_remaining_error`. -/
theorem binlog.events.Event.read_event_spec {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val)
    (r0 : core.result.Result T core.io.error.Error) (rest0 : io.ParseBuf)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = ok (r0, rest0)) :
    binlog.events.Event.read_event inst self = (match r0 with
      | .Err e => ok (.Err e)
      | .Ok x => if rest0.val = [] then ok (.Ok x) else do
          let e ← binlog.trusted.bytes_remaining_error T
          ok (.Err e)) := by
  sorry

/-- `read_event::<T>` fails (panics) exactly as `T`'s `parse` does. -/
theorem binlog.events.Event.read_event_fail {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val) (err : Error)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = fail err) :
    binlog.events.Event.read_event inst self = fail err := by
  sorry

/-- `read_data` on an unknown type code (41, ≥ 43): `Ok(None)`. -/
theorem binlog.events.Event.read_data_unknown (self : binlog.events.Event) (h : evTypeOfCode self.header.event_type.1.val = none) :
    binlog.events.Event.read_data self = ok (.Ok none) := by
  sorry

/-- `read_data` on a type it does not parse: the data-less variant of that type, or the variant holding the raw data. -/
theorem binlog.events.Event.read_data_unparsed (self : binlog.events.Event) (h : self.header.event_type.1.val ∈ edUnitCodes ++ edRawCodes) :
    binlog.events.Event.read_data self ⦃ r => ∃ d, r = .Ok (some d) ∧ edTypeCode d = self.header.event_type.1.val ∧
      (if self.header.event_type.1.val ∈ edUnitCodes then edUnit d = true else edRaw d = some self.data.val) ⦄ := by
  sorry

/-- `read_data` for type code 2: `read_event::<QueryEvent>`, wrapped in `EventData::QueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code2 (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.QueryEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 4: `read_event::<RotateEvent>`, wrapped in `EventData::RotateEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code4 (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RotateEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 5: `read_event::<IntvarEvent>`, wrapped in `EventData::IntvarEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code5 (self : binlog.events.Event) (h : self.header.event_type.1.val = 5) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IntvarEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 13: `read_event::<RandEvent>`, wrapped in `EventData::RandEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code13 (self : binlog.events.Event) (h : self.header.event_type.1.val = 13) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RandEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 14: `read_event::<UserVarEvent>`, wrapped in `EventData::UserVarEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code14 (self : binlog.events.Event) (h : self.header.event_type.1.val = 14) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.user_var_event.UserVarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.UserVarEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 16: `read_event::<XidEvent>`, wrapped in `EventData::XidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code16 (self : binlog.events.Event) (h : self.header.event_type.1.val = 16) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.XidEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 17: `read_event::<BeginLoadQueryEvent>`, wrapped in `EventData::BeginLoadQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code17 (self : binlog.events.Event) (h : self.header.event_type.1.val = 17) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.BeginLoadQueryEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 18: `read_event::<ExecuteLoadQueryEvent>`, wrapped in `EventData::ExecuteLoadQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code18 (self : binlog.events.Event) (h : self.header.event_type.1.val = 18) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.ExecuteLoadQueryEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 19: `read_event::<TableMapEvent>`, wrapped in `EventData::TableMapEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code19 (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TableMapEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 23: `read_event::<WriteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code23 (self : binlog.events.Event) (h : self.header.event_type.1.val = 23) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEventV1 x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 24: `read_event::<UpdateRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code24 (self : binlog.events.Event) (h : self.header.event_type.1.val = 24) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEventV1 x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 25: `read_event::<DeleteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code25 (self : binlog.events.Event) (h : self.header.event_type.1.val = 25) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEventV1 x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 26: `read_event::<IncidentEvent>`, wrapped in `EventData::IncidentEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code26 (self : binlog.events.Event) (h : self.header.event_type.1.val = 26) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IncidentEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 29: `read_event::<RowsQueryEvent>`, wrapped in `EventData::RowsQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code29 (self : binlog.events.Event) (h : self.header.event_type.1.val = 29) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsQueryEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 30: `read_event::<WriteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code30 (self : binlog.events.Event) (h : self.header.event_type.1.val = 30) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEvent x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 31: `read_event::<UpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code31 (self : binlog.events.Event) (h : self.header.event_type.1.val = 31) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEvent x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 32: `read_event::<DeleteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code32 (self : binlog.events.Event) (h : self.header.event_type.1.val = 32) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEvent x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 33: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code33 (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 34: `read_event::<AnonymousGtidEvent>`, wrapped in `EventData::AnonymousGtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code34 (self : binlog.events.Event) (h : self.header.event_type.1.val = 34) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.AnonymousGtidEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 35: `read_event::<PreviousGtidsEvent>`, wrapped in `EventData::PreviousGtidsEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code35 (self : binlog.events.Event) (h : self.header.event_type.1.val = 35) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.PreviousGtidsEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 39: `read_event::<PartialUpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::PartialUpdateRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code39 (self : binlog.events.Event) (h : self.header.event_type.1.val = 39) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.PartialUpdateRowsEvent x)))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 40: `read_event::<TransactionPayloadEvent>`, wrapped in `EventData::TransactionPayloadEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code40 (self : binlog.events.Event) (h : self.header.event_type.1.val = 40) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TransactionPayloadEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for type code 42: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code42 (self : binlog.events.Event) (h : self.header.event_type.1.val = 42) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err)) := by
  sorry

/-- `read_data` for a `FORMAT_DESCRIPTION_EVENT` (15): `read_event::<FormatDescriptionEvent>`, with this event's footer (`with_footer`). -/
theorem binlog.events.Event.read_data_code15 (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.FormatDescriptionEvent { x with footer := self.footer }))
        | .Err err => .Err err)) := by
  sorry

/-- End to end: the `EventData` of a query event (2) is the `queryRead` of its data (the post-header length from the event's FDE); an error iff that fails. -/
theorem binlog.events.Event.read_data_query_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match queryRead (postHeaderLen (fdeLens self.fde) .QUERY_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.QueryEvent x)) ∧ queryView x = v
      | none => okPart r = none ⦄ := by
  sorry

/-- End to end: the `EventData` of a rotate event (4): `rotateRead` of its data. -/
theorem binlog.events.Event.read_data_rotate_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rotateRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RotateEvent x)) ∧ rotateView x = v
      | none => okPart r = none ⦄ := by
  sorry

/-- End to end: the `EventData` of a format description event (15): `fdeRead` of its data, with the event's footer. -/
theorem binlog.events.Event.read_data_fde_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match fdeRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.FormatDescriptionEvent x)) ∧ fdeView x = v ∧ x.footer = self.footer
      | none => okPart r = none ⦄ := by
  sorry

/-- End to end: the `EventData` of a table map event (19): `tmRead` of its data. -/
theorem binlog.events.Event.read_data_table_map_wire (h64 : Target64) (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match tmRead (postHeaderLen (fdeLens self.fde) .TABLE_MAP_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.TableMapEvent x)) ∧ tmView x = v
      | none => okPart r = none ⦄ := by
  sorry

/-- End to end: the `EventData` of a rows event (23–25, 30–32, 39): the `RowsEventData` variant of its type, with `rowsRead` of its data (post-header lengths from the event's FDE). -/
theorem binlog.events.Event.read_data_rows_wire (h64 : Target64) (self : binlog.events.Event) (t : binlog.consts.EventType)
    (ht : evTypeOfCode self.header.event_type.1.val = some t) (hr : evTypeCode t ∈ [23, 24, 25, 30, 31, 32, 39])
    (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rowsRead t (postHeaderLen (fdeLens self.fde) t) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RowsEvent x)) ∧ rowsVariantCode x = evTypeCode t ∧ rowsView (rowsInner x) = v
      | none => okPart r = none ⦄ := by
  sorry

end mysql_common
