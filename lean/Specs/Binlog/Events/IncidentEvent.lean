import Proofs.Binlog.Events.IncidentEvent.IncidentEvent

/-!
# `src/binlog/events/incident_event.rs`
    `IncidentEvent` (`INCIDENT_EVENT`, code 26): the incident type (2) and a message with a 1-byte
    length. Covered: `new`, `incident_type`, `message_raw`, `with_incident_type`, `with_message`,
    `into_owned`, `SIZE`, `deserialize` (exact on any input), `serialize`, the round trip,
    `EVENT_TYPE`, `len`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`incidentEnc`, `incidentRead`,
    `incidentTypeCode`, `incidentTypeOfCode`, `u8Str`, `ReadsAs`), `Defs/LenEnc.lean`
    (`checkedLenPrefixed`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `message` (lossy UTF-8, excluded); the derived impls.

    **Behaviour to note.** A message is truncated to 255 bytes when written (and by `message_raw`).
    Bytes after the message are left unread (an error in `Event::read_event`).

    (Of these definitions, `incidentTypeCode`, `incidentTypeOfCode` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct IncidentEvent and its impls` -/

/-- `new(type, message)`: those fields. -/
recall binlog.events.incident_event.IncidentEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (t : binlog.consts.IncidentType) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.new into t m ⦃ e => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e = (incidentTypeCode t, cowList c) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.new_spec`

/-- `incident_type`: the known type with the stored code, or the raw code as an error. -/
recall binlog.events.incident_event.IncidentEvent.impl.incident_type_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.impl.incident_type e ⦃ r => match incidentTypeOfCode e.incident_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err e.incident_type.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.impl.incident_type_spec`

/-- `message_raw`: the message, its first 255 bytes (the effective bytes of a `U8Bytes`). -/
recall binlog.events.incident_event.IncidentEvent.message_raw_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.message_raw e ⦃ s => s.val = (cowList e.message.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.message_raw_spec`

/-- `with_incident_type`: replaces the type. -/
recall binlog.events.incident_event.IncidentEvent.with_incident_type_spec (e : binlog.events.incident_event.IncidentEvent) (t : binlog.consts.IncidentType) :
    binlog.events.incident_event.IncidentEvent.with_incident_type e t ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (incidentTypeCode t, cowList e.message.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.with_incident_type_spec`

/-- `with_message`: replaces the message. -/
recall binlog.events.incident_event.IncidentEvent.with_message_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.incident_event.IncidentEvent) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.with_message into e m ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (e.incident_type.1.val, cowList c) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.with_message_spec`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.incident_event.IncidentEvent.into_owned_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.into_owned e ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; `incidentRead` (the raw type, then the length-prefixed message; the rest is left). -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) (incidentRead buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `incidentEnc`. -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.incident_event.IncidentEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (incidentEnc e).length ≤ Usize.max) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ incidentEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for a message of at most 255 bytes. -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.incident_event.IncidentEvent) (hm : (cowList e.message.1).length ≤ 255) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = incidentEnc e ++ tail) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) = some ((fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `INCIDENT_EVENT` (26). -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INCIDENT_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: the length of what `serialize` writes (`incidentEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.incident_event.IncidentEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (incidentEnc e).length evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

end mysql_common
