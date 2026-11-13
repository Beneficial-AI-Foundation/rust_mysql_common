import Proofs.Binlog.Events.IntvarEvent.IntvarEvent

/-!
# `src/binlog/events/intvar_event.rs`
    `IntvarEvent` (`INTVAR_EVENT`, code 5): the subtype (1: `INVALID_INT_EVENT` 0,
    `LAST_INSERT_ID_EVENT` 1, `INSERT_ID_EVENT` 2) and the value (8). Covered: `new`, `subtype`,
    `value`, `with_subtype`, `with_value`, `SIZE`, `deserialize` (exact with 9 bytes, the panic
    otherwise), `ParseBuf::parse` (total), `serialize`, the round trip, `EVENT_TYPE`, `len`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`intvarEnc`, `intvarRead`, `intvarTypeCode`,
    `intvarTypeOfCode`, `ReadsAs`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The derived `Debug`/`Clone`/`PartialEq`/`Hash`.

    **Behaviour to note.** `deserialize` does not check the length (`SIZE` is `Some(9)`, it uses
    `parse_unchecked`): called directly on fewer than 9 bytes it panics unless it first meets an
    unknown subtype; `parse` (as `Event::read_event` uses it) checks.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct IntvarEvent and its impls` -/

/-- `new(subtype, value)`: those fields. -/
recall binlog.events.intvar_event.IntvarEvent.new_spec (t : binlog.consts.IntvarEventType) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.new t value ⦃ e => e.subtype.1 = t ∧ e.value.1 = value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.new_spec`

/-- `subtype`: the subtype. -/
recall binlog.events.intvar_event.IntvarEvent.impl.subtype_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.subtype e = ok e.subtype.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.impl.subtype_eq`

/-- `value`: the value. -/
recall binlog.events.intvar_event.IntvarEvent.impl.value_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.value e = ok e.value.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.impl.value_eq`

/-- `with_subtype`: replaces the subtype. -/
recall binlog.events.intvar_event.IntvarEvent.with_subtype_spec (e : binlog.events.intvar_event.IntvarEvent) (t : binlog.consts.IntvarEventType) :
    binlog.events.intvar_event.IntvarEvent.with_subtype e t ⦃ e' => e'.subtype.1 = t ∧ e'.value = e.value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.with_subtype_spec`

/-- `with_value`: replaces the value. -/
recall binlog.events.intvar_event.IntvarEvent.with_value_spec (e : binlog.events.intvar_event.IntvarEvent) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.with_value e value ⦃ e' => e'.subtype = e.subtype ∧ e'.value.1 = value ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.with_value_spec`

/-- `MyDeserialize::SIZE` is `some 9#usize`. -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 9#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize` on at least 9 bytes: `intvarRead` (an unknown subtype is an error). -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 9 ≤ buf.length) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MyDeserialize` panics on fewer than 9 bytes, unless the first byte is an unknown subtype (then it is an error). -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 9)
    (hs : ∀ b, buf.val.head? = some b → intvarTypeOfCode b.val ≠ none) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics`

/-- `buf.parse::<IntvarEvent>(ctx)`: total (`SIZE` checked first); `intvarRead`. -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec`

/-- `MySerialize`: appends the layout `intvarEnc`. -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.intvar_event.IntvarEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (intvarEnc e).length ≤ Usize.max) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ intvarEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip. -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.intvar_event.IntvarEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = intvarEnc e ++ tail) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `INTVAR_EVENT` (5). -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INTVAR_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: 9 (= the length of `intvarEnc`). -/
recall binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.intvar_event.IntvarEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 9#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq`

end mysql_common
