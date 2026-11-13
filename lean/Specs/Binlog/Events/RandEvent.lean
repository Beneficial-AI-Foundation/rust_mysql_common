import Proofs.Binlog.Events.RandEvent.RandEvent

/-!
# `src/binlog/events/rand_event.rs`
    `RandEvent` (`RAND_EVENT`, code 13): `seed1` (8), `seed2` (8) (public fields). Covered: `SIZE`,
    `deserialize` (exact with 16 bytes, the panic otherwise), `parse` (total), `serialize`, the
    round trip, `EVENT_TYPE`, `len` (a bug).

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`randEnc`, `ReadsAs`, `readLE`).
    **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The derived `Debug`/`Clone`/`PartialEq`/`Hash`.

    **Behaviour to note (bug).** **`BinlogStruct::len` returns 8, but `serialize` writes 16 bytes**
    (`len_eq`): an `Event` length computed from it is wrong. `deserialize` panics on fewer than
    16 bytes (unchecked, as `IntvarEvent`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RandEvent and its impls` -/

/-- `MyDeserialize::SIZE` is `some 16#usize`. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 16#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize` on at least 16 bytes: the two seeds. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) = some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧ rest.val = buf.val.drop 16 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MyDeserialize` panics on fewer than 16 bytes. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 16) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics`

/-- `buf.parse::<RandEvent>(ctx)`: total; an error on fewer than 16 bytes. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) (if 16 ≤ buf.length then some ((leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)), buf.val.drop 16) else none) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec`

/-- `MySerialize`: appends the layout `randEnc`. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rand_event.RandEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (randEnc e).length ≤ Usize.max) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ randEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip. -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rand_event.RandEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = randEnc e ++ tail) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `RAND_EVENT` (13). -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .RAND_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- **Upstream bug:** `BinlogStruct::len` is 8, but the event data is 16 bytes (`randEnc`, two `u64`). -/
recall binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.rand_event.RandEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 8#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq`

end mysql_common
