import Proofs.Binlog.Events.RotateEvent.RotateEvent

/-!
# `src/binlog/events/rotate_event.rs`
    `RotateEvent` (`ROTATE_EVENT`, code 4): `position` (8) and the next binlog's name (the rest of
    the data). Covered: `new`, `with_position`, `with_name`, `position`, `name_raw`, `is_fake`,
    `into_owned`, `MyDeserialize` (exact on any input), `MySerialize`, the round trip,
    `BinlogStruct::len` (exact), `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`rotateEnc`, `rotateRead`, `rotateView`,
    `ReadsAs`, `evLenCap`), `Defs/Bytes.lean`. **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `name` (lossy UTF-8 `Cow<str>`, excluded from the translation); the derived
    `Debug`/`Clone`/`PartialEq`/`Hash`.

    **Behaviour to note.** The reader ignores the FDE's post-header length for this type (always 8).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RotateEvent and its impls` -/

/-- `new(position, name)`: those fields (`name` converted with `into`). -/
recall binlog.events.rotate_event.RotateEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (position : U64) (nm : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into nm = ok c) :
    binlog.events.rotate_event.RotateEvent.new into position nm ⦃ e => rotateView e = (position.val, cowList c) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.new_spec`

/-- `with_position`: replaces the position. -/
recall binlog.events.rotate_event.RotateEvent.with_position_spec (e : binlog.events.rotate_event.RotateEvent) (position : U64) :
    binlog.events.rotate_event.RotateEvent.with_position e position ⦃ e' => rotateView e' = (position.val, cowList e.«name».1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.with_position_spec`

/-- `with_name`: replaces the name. -/
recall binlog.events.rotate_event.RotateEvent.with_name_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (e : binlog.events.rotate_event.RotateEvent) (nm : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into nm = ok c) :
    binlog.events.rotate_event.RotateEvent.with_name into e nm ⦃ e' => rotateView e' = (e.position.1.val, cowList c) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.with_name_spec`

/-- `position`: the position. -/
recall binlog.events.rotate_event.RotateEvent.impl.position_eq (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.impl.position e = ok e.position.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.impl.position_eq`

/-- `name_raw`: the name bytes. -/
recall binlog.events.rotate_event.RotateEvent.name_raw_spec (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.name_raw e ⦃ s => s.val = cowList e.«name».1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.name_raw_spec`

/-- `is_fake`: whether the position is 0 (a fake rotate event, sent at the start of a dump). -/
recall binlog.events.rotate_event.RotateEvent.is_fake_eq (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.is_fake e = ok (decide (e.position.1.val = 0))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.is_fake_eq`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.rotate_event.RotateEvent.into_owned_spec (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.into_owned e ⦃ e' => rotateView e' = rotateView e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; `rotateRead` (8 bytes of position, the name as the rest). -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rotateView (rotateRead buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `rotateEnc`. -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rotate_event.RotateEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (rotateEnc e).length ≤ Usize.max) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rotateEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: the data `serialize` writes reads back as the same event. -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rotate_event.RotateEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = rotateEnc e) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map rotateView = some (rotateView e) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `ROTATE_EVENT` (4). -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ROTATE_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: the length of what `serialize` writes (`rotateEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rotate_event.RotateEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (rotateEnc e).length evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

end mysql_common
