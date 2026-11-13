import Defs

/-! Statements for `struct IncidentEvent and its impls` (spec file: `Specs/Binlog/Events/IncidentEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(type, message)`: those fields. -/
theorem binlog.events.incident_event.IncidentEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (t : binlog.consts.IncidentType) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.new into t m ⦃ e => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e = (incidentTypeCode t, cowList c) ⦄ := by
  sorry

/-- `incident_type`: the known type with the stored code, or the raw code as an error. -/
theorem binlog.events.incident_event.IncidentEvent.impl.incident_type_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.impl.incident_type e ⦃ r => match incidentTypeOfCode e.incident_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err e.incident_type.1 ⦄ := by
  sorry

/-- `message_raw`: the message, its first 255 bytes (the effective bytes of a `U8Bytes`). -/
theorem binlog.events.incident_event.IncidentEvent.message_raw_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.message_raw e ⦃ s => s.val = (cowList e.message.1).take 255 ⦄ := by
  sorry

/-- `with_incident_type`: replaces the type. -/
theorem binlog.events.incident_event.IncidentEvent.with_incident_type_spec (e : binlog.events.incident_event.IncidentEvent) (t : binlog.consts.IncidentType) :
    binlog.events.incident_event.IncidentEvent.with_incident_type e t ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (incidentTypeCode t, cowList e.message.1) ⦄ := by
  sorry

/-- `with_message`: replaces the message. -/
theorem binlog.events.incident_event.IncidentEvent.with_message_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.incident_event.IncidentEvent) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.with_message into e m ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (e.incident_type.1.val, cowList c) ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.incident_event.IncidentEvent.into_owned_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.into_owned e ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; `incidentRead` (the raw type, then the length-prefixed message; the rest is left). -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) (incidentRead buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `incidentEnc`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.incident_event.IncidentEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (incidentEnc e).length ≤ Usize.max) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ incidentEnc e ⦄ := by
  sorry

/-- Round trip, for a message of at most 255 bytes. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.incident_event.IncidentEvent) (hm : (cowList e.message.1).length ≤ 255) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = incidentEnc e ++ tail) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) = some ((fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e) ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `INCIDENT_EVENT` (26). -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INCIDENT_EVENT := by
  sorry

/-- `BinlogStruct::len`: the length of what `serialize` writes (`incidentEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.incident_event.IncidentEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (incidentEnc e).length evLenCap ⦄ := by
  sorry

end mysql_common
