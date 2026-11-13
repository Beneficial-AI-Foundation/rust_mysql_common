import Proofs.Binlog.Events.Mod.Event
import Proofs.Binlog.Events.Mod.BinlogEventHeader
import Proofs.Binlog.Events.Mod.BinlogEventFooter
import Proofs.Binlog.Events.Mod.EventData
import Proofs.Binlog.Events.Mod.RowsEventData

/-!
# `src/binlog/events/mod.rs`
    The raw event (`Event`: accessors, `len`, the `read_event` / `read_data` dispatch), the
    common header (`BinlogEventHeader`), the footer (`BinlogEventFooter`), `EventData` and
    `RowsEventData`. Headlines: the header's exact layout and round trip; `read_event` parses the
    data with the type's reader (`parse`, so `SIZE` checked) and fails if bytes are left;
    `read_data` dispatches on the type code exactly as the MySQL type list (unknown codes, 41 and
    ≥ 43, give `None`); end to end, the `EventData` of a query, rotate, FDE, table map or rows event
    is what the format reader of its data gives. Every event type's own statements are in
    `Specs/Binlog/Events/*.lean`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155, in particular 150: `saturating_add` in `len`, 151–152). The
    table map and rows readers take `Target64` (they cast wire counts with `as usize`).

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. `read_event` requires `19 + data.len()` not to overflow (`hlen`; true for every
    event `Event::read` builds).

    **Definitions used.** `Defs/BinlogEvents.lean` (`evHeaderEnc`, `footerAlg`, `evHasChecksum`,
    `eventLen`, `edRaw`, `edUnit`, `edUnitCodes`, `edRawCodes`, `edTypeCode`, `rowsInner`,
    `rowsVariantCode`, `rowsView`, `rowsEnc`, `rowsRead`, `queryRead`, `queryView`, `rotateRead`,
    `rotateView`, `fdeRead`, `fdeView`, `tmRead`, `tmView`, `gtidRead`, `GtidView`, `gtidView`,
    `postHeaderLen`, `fdeLens`), `Defs/BinlogCore.lean` (`eventTypeCode`, `eventTypeOfCode`,
    `eventFlagsAll`, `rowsEventFlagsAll`, `checksumAlgCode`, `checksumAlgOfCode`),
    `Defs/Bytes.lean`.

    **Trusted axioms.** None of namespace `Trusted`. Opaque (nothing assumed): `io::Error`, and
    `binlog::trusted::bytes_remaining_error` (the error of `read_event` when bytes are left: the
    statements give it as that call), and, through the dispatch equations only, the opaque
    `UserVarEvent` and `TransactionPayloadEvent` readers and the tagged GTID reader.

    **Not covered.** `Event::read`, `write`, `calc_checksum` (I/O, crc32; excluded),
    `BinlogEventFooter::read` (version parsing with `split_version`; excluded), the `bitvec`
    views `columns_before_image` / `columns_after_image` (excluded), `RowsEventRows`'s iterator
    (excluded: `BinlogRow` parsing). `EventData::into_owned` is stated only for the variant and raw
    data it keeps (each event's `into_owned` has its own statement). The derived impls.

    **Behaviour to note.** `read_data` maps `ENUM_END_EVENT`'s variant `UnknownEvent` only from
    code 0 (43 is unknown on the wire); `GTID_TAGGED_LOG_EVENT` (42) gives `EventData::GtidEvent`.
    `Event::len` counts a footer only for a known checksum algorithm and caps at `u32::MAX - 19`.
    The checksum is reported for an FDE whenever the footer names an algorithm, `OFF` included.
    * **`checksum()`, `len` and `write` ignore `checksum_enabled`**, while `Event::read` honours it
      when stripping the checksum: an event read with checksums disabled (inside a
      `TRANSACTION_PAYLOAD_EVENT`) under a non-`OFF` algorithm reports `Some([0; 4])` as its
      checksum and 4 extra bytes of length (`checksum_eq`, `len_spec`).
    * **`Event::read` (not translated) panics instead of returning an error** on input shorter than
      the header's `event_size` (`read_exact(..).unwrap()`), and on event data shorter than its
      checksum footer (`data.len() - 4` underflows, e.g. `event_size` 19 under a CRC32 FDE).
    * `read_data` of a GTID event that carries `commit_group_ticket` (MySQL 8.0.33+) is an error:
      the GTID reader leaves those bytes, so `read_event` reports bytes remaining
      (`read_data_gtid_leftover`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct Event and its impls` -/

/-- `fde`: the format description event the event was read with. -/
recall binlog.events.Event.impl.fde_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.fde self = ok self.fde

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.impl.fde_eq`

/-- `header`: the common header. -/
recall binlog.events.Event.impl.header_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.header self = ok self.header

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.impl.header_eq`

/-- `data`: the event data (footer stripped). -/
recall binlog.events.Event.impl.data_spec (self : binlog.events.Event) :
    binlog.events.Event.impl.data self ⦃ s => s.val = self.data.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.impl.data_spec`

/-- `footer`. -/
recall binlog.events.Event.impl.footer_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.footer self = ok self.footer

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.impl.footer_eq`

/-- `checksum`: the stored checksum iff the event carries one (`evHasChecksum`). -/
recall binlog.events.Event.impl.checksum_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.checksum self = ok (if evHasChecksum self.footer self.header.event_type.1.val then some self.checksum else none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.impl.checksum_eq`

/-- `len` (private, used by `write`): `eventLen`. -/
recall binlog.events.Event.len_spec (self : binlog.events.Event) (v : binlog.consts.BinlogVersion) :
    binlog.events.Event.len self v ⦃ n => n.val = eventLen self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.len_spec`

/-- `read_event::<T>`: `T` is parsed from the data with `parse` (so `T::SIZE` is checked) in the context (`19 + data.len()`, the FDE, the raw type); its error is passed on; a success is `Ok` iff no bytes are left, and otherwise the (opaque) `bytes_remaining_error`. -/
recall binlog.events.Event.read_event_spec {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val)
    (r0 : core.result.Result T core.io.error.Error) (rest0 : io.ParseBuf)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = ok (r0, rest0)) :
    binlog.events.Event.read_event inst self = (match r0 with
      | .Err e => ok (.Err e)
      | .Ok x => if rest0.val = [] then ok (.Ok x) else do
          let e ← binlog.trusted.bytes_remaining_error T
          ok (.Err e))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_event_spec`

/-- `read_event::<T>` fails (panics) exactly as `T`'s `parse` does. -/
recall binlog.events.Event.read_event_fail {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val) (err : Error)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = fail err) :
    binlog.events.Event.read_event inst self = fail err

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_event_fail`

/-- `read_data` on an unknown type code (41, ≥ 43): `Ok(None)`. -/
recall binlog.events.Event.read_data_unknown (self : binlog.events.Event) (h : eventTypeOfCode self.header.event_type.1.val = none) :
    binlog.events.Event.read_data self = ok (.Ok none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_unknown`

/-- `read_data` on a type it does not parse: the data-less variant of that type, or the variant holding the raw data. -/
recall binlog.events.Event.read_data_unparsed (self : binlog.events.Event) (h : self.header.event_type.1.val ∈ edUnitCodes ++ edRawCodes) :
    binlog.events.Event.read_data self ⦃ r => ∃ d, r = .Ok (some d) ∧ edTypeCode d = self.header.event_type.1.val ∧
      (if self.header.event_type.1.val ∈ edUnitCodes then edUnit d = true else edRaw d = some self.data.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_unparsed`

/-- `read_data` for type code 2: `read_event::<QueryEvent>`, wrapped in `EventData::QueryEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code2 (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.QueryEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code2`

/-- `read_data` for type code 4: `read_event::<RotateEvent>`, wrapped in `EventData::RotateEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code4 (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RotateEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code4`

/-- `read_data` for type code 5: `read_event::<IntvarEvent>`, wrapped in `EventData::IntvarEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code5 (self : binlog.events.Event) (h : self.header.event_type.1.val = 5) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IntvarEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code5`

/-- `read_data` for type code 13: `read_event::<RandEvent>`, wrapped in `EventData::RandEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code13 (self : binlog.events.Event) (h : self.header.event_type.1.val = 13) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RandEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code13`

/-- `read_data` for type code 14: `read_event::<UserVarEvent>`, wrapped in `EventData::UserVarEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code14 (self : binlog.events.Event) (h : self.header.event_type.1.val = 14) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.user_var_event.UserVarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.UserVarEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code14`

/-- `read_data` for type code 16: `read_event::<XidEvent>`, wrapped in `EventData::XidEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code16 (self : binlog.events.Event) (h : self.header.event_type.1.val = 16) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.XidEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code16`

/-- `read_data` for type code 17: `read_event::<BeginLoadQueryEvent>`, wrapped in `EventData::BeginLoadQueryEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code17 (self : binlog.events.Event) (h : self.header.event_type.1.val = 17) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.BeginLoadQueryEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code17`

/-- `read_data` for type code 18: `read_event::<ExecuteLoadQueryEvent>`, wrapped in `EventData::ExecuteLoadQueryEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code18 (self : binlog.events.Event) (h : self.header.event_type.1.val = 18) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.ExecuteLoadQueryEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code18`

/-- `read_data` for type code 19: `read_event::<TableMapEvent>`, wrapped in `EventData::TableMapEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code19 (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TableMapEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code19`

/-- `read_data` for type code 23: `read_event::<WriteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEventV1`) (its errors passed on). -/
recall binlog.events.Event.read_data_code23 (self : binlog.events.Event) (h : self.header.event_type.1.val = 23) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEventV1 x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code23`

/-- `read_data` for type code 24: `read_event::<UpdateRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEventV1`) (its errors passed on). -/
recall binlog.events.Event.read_data_code24 (self : binlog.events.Event) (h : self.header.event_type.1.val = 24) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEventV1 x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code24`

/-- `read_data` for type code 25: `read_event::<DeleteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEventV1`) (its errors passed on). -/
recall binlog.events.Event.read_data_code25 (self : binlog.events.Event) (h : self.header.event_type.1.val = 25) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEventV1 x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code25`

/-- `read_data` for type code 26: `read_event::<IncidentEvent>`, wrapped in `EventData::IncidentEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code26 (self : binlog.events.Event) (h : self.header.event_type.1.val = 26) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IncidentEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code26`

/-- `read_data` for type code 29: `read_event::<RowsQueryEvent>`, wrapped in `EventData::RowsQueryEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code29 (self : binlog.events.Event) (h : self.header.event_type.1.val = 29) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsQueryEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code29`

/-- `read_data` for type code 30: `read_event::<WriteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEvent`) (its errors passed on). -/
recall binlog.events.Event.read_data_code30 (self : binlog.events.Event) (h : self.header.event_type.1.val = 30) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEvent x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code30`

/-- `read_data` for type code 31: `read_event::<UpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEvent`) (its errors passed on). -/
recall binlog.events.Event.read_data_code31 (self : binlog.events.Event) (h : self.header.event_type.1.val = 31) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEvent x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code31`

/-- `read_data` for type code 32: `read_event::<DeleteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEvent`) (its errors passed on). -/
recall binlog.events.Event.read_data_code32 (self : binlog.events.Event) (h : self.header.event_type.1.val = 32) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEvent x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code32`

/-- `read_data` for type code 33: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code33 (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code33`

/-- `read_data` for type code 34: `read_event::<AnonymousGtidEvent>`, wrapped in `EventData::AnonymousGtidEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code34 (self : binlog.events.Event) (h : self.header.event_type.1.val = 34) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.AnonymousGtidEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code34`

/-- `read_data` for type code 35: `read_event::<PreviousGtidsEvent>`, wrapped in `EventData::PreviousGtidsEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code35 (self : binlog.events.Event) (h : self.header.event_type.1.val = 35) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.PreviousGtidsEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code35`

/-- `read_data` for type code 39: `read_event::<PartialUpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::PartialUpdateRowsEvent`) (its errors passed on). -/
recall binlog.events.Event.read_data_code39 (self : binlog.events.Event) (h : self.header.event_type.1.val = 39) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.PartialUpdateRowsEvent x)))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code39`

/-- `read_data` for type code 40: `read_event::<TransactionPayloadEvent>`, wrapped in `EventData::TransactionPayloadEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code40 (self : binlog.events.Event) (h : self.header.event_type.1.val = 40) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TransactionPayloadEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code40`

/-- `read_data` for type code 42: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
recall binlog.events.Event.read_data_code42 (self : binlog.events.Event) (h : self.header.event_type.1.val = 42) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code42`

/-- `read_data` for a `FORMAT_DESCRIPTION_EVENT` (15): `read_event::<FormatDescriptionEvent>`, with this event's footer (`with_footer`). -/
recall binlog.events.Event.read_data_code15 (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.FormatDescriptionEvent { x with footer := self.footer }))
        | .Err err => .Err err))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_code15`

/-- End to end: the `EventData` of a query event (2) is the `queryRead` of its data (the post-header length from the event's FDE); an error iff that fails. -/
recall binlog.events.Event.read_data_query_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match queryRead (postHeaderLen (fdeLens self.fde) .QUERY_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.QueryEvent x)) ∧ queryView x = v
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_query_wire`

/-- End to end: the `EventData` of a rotate event (4): `rotateRead` of its data. -/
recall binlog.events.Event.read_data_rotate_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rotateRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RotateEvent x)) ∧ rotateView x = v
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_rotate_wire`

/-- End to end: the `EventData` of a format description event (15): `fdeRead` of its data, with the event's footer. -/
recall binlog.events.Event.read_data_fde_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match fdeRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.FormatDescriptionEvent x)) ∧ fdeView x = v ∧ x.footer = self.footer
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_fde_wire`

/-- End to end: the `EventData` of a table map event (19): `tmRead` of its data. -/
recall binlog.events.Event.read_data_table_map_wire (h64 : Target64) (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match tmRead (postHeaderLen (fdeLens self.fde) .TABLE_MAP_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.TableMapEvent x)) ∧ tmView x = v
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_table_map_wire`

/-- End to end: the `EventData` of a rows event (23–25, 30–32, 39): the `RowsEventData` variant of its type, with `rowsRead` of its data (post-header lengths from the event's FDE). -/
recall binlog.events.Event.read_data_rows_wire (h64 : Target64) (self : binlog.events.Event) (t : binlog.consts.EventType)
    (ht : eventTypeOfCode self.header.event_type.1.val = some t) (hr : eventTypeCode t ∈ [23, 24, 25, 30, 31, 32, 39])
    (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rowsRead t (postHeaderLen (fdeLens self.fde) t) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RowsEvent x)) ∧ rowsVariantCode x = eventTypeCode t ∧ rowsView (rowsInner x) = v
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_rows_wire`

/-- End to end: the `EventData` of a GTID event (33) whose data the untagged GTID reader consumes entirely: `gtidRead`; an error iff that fails. -/
recall binlog.events.Event.read_data_gtid_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) (hlen : self.data.length + 19 ≤ Usize.max)
    (hg : ∀ v b bs, gtidRead self.data.val ≠ some (v, b :: bs)) :
    binlog.events.Event.read_data self ⦃ r => match gtidRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.GtidEvent x)) ∧ gtidView x = v ∧ x.tag = none
      | none => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_gtid_wire`

/-- A GTID event (33) whose data has bytes after what the GTID reader reads (e.g. MySQL 8.0.33+'s `commit_group_ticket`): `read_data` is the (opaque) bytes-remaining error. -/
recall binlog.events.Event.read_data_gtid_leftover (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) (hlen : self.data.length + 19 ≤ Usize.max)
    (v : GtidView) (b : U8) (bs : List U8) (hg : gtidRead self.data.val = some (v, b :: bs)) :
    binlog.events.Event.read_data self = (do
      let e ← binlog.trusted.bytes_remaining_error binlog.events.gtid_event.GtidEvent
      ok (.Err e))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.Event.read_data_gtid_leftover`

/-! ### `struct BinlogEventHeader and its impls` -/

/-- `LEN`: 19. -/
recall binlog.events.BinlogEventHeader.LEN_eq :
    binlog.events.BinlogEventHeader.LEN = 19#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.LEN_eq`

/-- `new`: those fields (the type as its code, the flags' bits). -/
recall binlog.events.BinlogEventHeader.new_spec (ts : U32) (t : binlog.consts.EventType) (sid size pos : U32) (fl : binlog.consts.EventFlags) :
    binlog.events.BinlogEventHeader.new ts t sid size pos fl ⦃ h => h.timestamp.1 = ts ∧ h.event_type.1.val = eventTypeCode t ∧
      h.server_id.1 = sid ∧ h.event_size.1 = size ∧ h.log_pos.1 = pos ∧ h.flags.1 = fl ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.new_spec`

/-- `timestamp`. -/
recall binlog.events.BinlogEventHeader.impl.timestamp_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.timestamp h = ok h.timestamp.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.timestamp_eq`

/-- `event_type_raw`: the type byte. -/
recall binlog.events.BinlogEventHeader.event_type_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.event_type_raw h = ok h.event_type.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.event_type_raw_eq`

/-- `event_type`: the known type with that code, or the raw byte as an error. -/
recall binlog.events.BinlogEventHeader.impl.event_type_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_type h ⦃ r => match eventTypeOfCode h.event_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err h.event_type.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.event_type_spec`

/-- `server_id`. -/
recall binlog.events.BinlogEventHeader.impl.server_id_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.server_id h = ok h.server_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.server_id_eq`

/-- `event_size`. -/
recall binlog.events.BinlogEventHeader.impl.event_size_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_size h = ok h.event_size.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.event_size_eq`

/-- `log_pos`. -/
recall binlog.events.BinlogEventHeader.impl.log_pos_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.log_pos h = ok h.log_pos.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.log_pos_eq`

/-- `flags`: the known flag bits (`from_bits_truncate`). -/
recall binlog.events.BinlogEventHeader.impl.flags_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.flags h ⦃ f => f.val = h.flags.1.val &&& eventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.impl.flags_spec`

/-- `flags_raw`: all the flag bits. -/
recall binlog.events.BinlogEventHeader.flags_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.flags_raw h = ok h.flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.flags_raw_eq`

/-- `MyDeserialize::SIZE` is `Some(19)`. -/
recall binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 19#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize`: total; on at least 19 bytes the header whose layout is the first 19 (`evHeaderEnc` is injective, so this determines it), else an error with the buffer unchanged. -/
recall binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      if 19 ≤ buf.length then (okPart r).map evHeaderEnc = some (buf.val.take 19) ∧ rest.val = buf.val.drop 19
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize`: appends the 19-byte header. -/
recall binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize_spec (h : binlog.events.BinlogEventHeader) (buf : alloc.vec.Vec U8) (hb : buf.length + 19 ≤ Usize.max) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize h buf ⦃ buf' => buf'.val = buf.val ++ evHeaderEnc h ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: a written header reads back as itself. -/
recall binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h : binlog.events.BinlogEventHeader) (tail : List U8) (buf : io.ParseBuf) (hb : buf.val = evHeaderEnc h ++ tail) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => okPart r = some h ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct BinlogEventFooter and its impls` -/

/-- `BINLOG_CHECKSUM_ALG_DESC_LEN`: 1. -/
recall binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN_eq :
    binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN = 1#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN_eq`

/-- `BINLOG_CHECKSUM_LEN`: 4. -/
recall binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN_eq :
    binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN = 4#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN_eq`

/-- `new(alg)`: that algorithm, checksums enabled. -/
recall binlog.events.BinlogEventFooter.new_spec (alg : binlog.consts.BinlogChecksumAlg) :
    binlog.events.BinlogEventFooter.new alg ⦃ f => footerAlg f = some (checksumAlgCode alg) ∧ f.checksum_enabled = true ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.new_spec`

/-- `get_checksum_alg`: `Ok(None)` without an algorithm, the known algorithm, or the raw code as an error. -/
recall binlog.events.BinlogEventFooter.get_checksum_alg_spec (f : binlog.events.BinlogEventFooter) :
    binlog.events.BinlogEventFooter.get_checksum_alg f ⦃ r => match footerAlg f with
      | none => r = .Ok none
      | some a => match checksumAlgOfCode a with
        | some alg => r = .Ok (some alg)
        | none => r = .Err (byte a) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.get_checksum_alg_spec`

/-- `get_checksum_enabled`. -/
recall binlog.events.BinlogEventFooter.get_checksum_enabled_eq (f : binlog.events.BinlogEventFooter) :
    binlog.events.BinlogEventFooter.get_checksum_enabled f = ok f.checksum_enabled

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.get_checksum_enabled_eq`

/-- `set_checksum_enabled`. -/
recall binlog.events.BinlogEventFooter.set_checksum_enabled_eq (f : binlog.events.BinlogEventFooter) (b : Bool) :
    binlog.events.BinlogEventFooter.set_checksum_enabled f b = ok { f with checksum_enabled := b }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.set_checksum_enabled_eq`

/-- `Default`: algorithm `OFF` (0), checksums enabled. -/
recall binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default_spec :
    binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default ⦃ f => footerAlg f = some 0 ∧ f.checksum_enabled = true ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default_spec`

/-! ### `enum EventData and its impls` -/

/-- `into_owned`: the same variant (type code), and the same raw data for the uninterpreted variants. -/
recall binlog.events.EventData.into_owned_spec (d : binlog.events.EventData) :
    binlog.events.EventData.into_owned d ⦃ d' => edTypeCode d' = edTypeCode d ∧ edRaw d' = edRaw d ∧ edUnit d' = edUnit d ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.EventData.into_owned_spec`

/-- `MySerialize` of a data-less variant: writes nothing. -/
recall binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_unit (d : binlog.events.EventData) (h : edUnit d = true) (buf : alloc.vec.Vec U8) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf = ok buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_unit`

/-- `MySerialize` of an uninterpreted variant: appends its raw data. -/
recall binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_raw (d : binlog.events.EventData) (bs : List U8) (h : edRaw d = some bs) (buf : alloc.vec.Vec U8) (hb : buf.length + bs.length ≤ Usize.max) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ bs ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_raw`

/-- `MySerialize` of a parsed variant: the event's own `serialize`. -/
recall binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_parsed (buf : alloc.vec.Vec U8) :
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
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RowsEvent x) buf = binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize x buf)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_parsed`

/-! ### `enum RowsEventData and its impls` -/

/-- `table_id`: the wrapped event's. -/
recall binlog.events.RowsEventData.table_id_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.table_id d = ok (rowsInner d).table_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.table_id_eq`

/-- `num_columns`: the wrapped event's. -/
recall binlog.events.RowsEventData.num_columns_eq (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.num_columns d = ok (rowsInner d).num_columns.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.num_columns_eq`

/-- `rows_data`: the wrapped event's raw rows. -/
recall binlog.events.RowsEventData.rows_data_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.rows_data d ⦃ s => s.val = cowList (rowsInner d).rows_data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.rows_data_spec`

/-- `flags`: the wrapped event's known flag bits. -/
recall binlog.events.RowsEventData.flags_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.flags d ⦃ f => f.val = (rowsInner d).flags.1.val &&& rowsEventFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.flags_spec`

/-- `rows(tme)`: an iterator over the wrapped event's rows data, with that table map. -/
recall binlog.events.RowsEventData.rows_spec (d : binlog.events.RowsEventData) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.RowsEventData.rows d tme ⦃ it => it.rows_event = rowsInner d ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList (rowsInner d).rows_data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.rows_spec`

/-- `into_owned`: the same variant and fields. -/
recall binlog.events.RowsEventData.into_owned_spec (d : binlog.events.RowsEventData) :
    binlog.events.RowsEventData.into_owned d ⦃ d' => rowsVariantCode d' = rowsVariantCode d ∧ rowsView (rowsInner d') = rowsView (rowsInner d) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.into_owned_spec`

/-- `MySerialize`: the wrapped event's layout. -/
recall binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize_spec (d : binlog.events.RowsEventData) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc (rowsInner d)).length ≤ Usize.max) :
    binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc (rowsInner d) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize_spec`

end mysql_common
