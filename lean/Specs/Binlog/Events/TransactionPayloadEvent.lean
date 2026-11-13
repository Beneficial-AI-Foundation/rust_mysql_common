import Proofs.Binlog.Events.TransactionPayloadEvent.TransactionPayloadEvent

/-!
# `src/binlog/events/transaction_payload_event.rs`
    `TransactionPayloadEvent` (`TRANSACTION_PAYLOAD_EVENT`, code 40), header fields only: `new`,
    `with_*`, `payload_size`, `payload_raw`, `algorithm`, `uncompressed_size`, `into_owned`,
    `serialize` (exact), `len`, `SIZE`, `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`tpEnc`, `tpField`, `txCompressionCode`,
    `evLenCap`), `Defs/LenEnc.lean` (`lenencInt`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `deserialize` (opaque in Cargo.toml: it walks the header with
    `read_lenenc_int` (`ReadMysqlExt`) and `try_from(..).unwrap()`); `SIZE` is a hand-written model
    (`None`, `FunsExternal.lean`); the zstd decompression API (`decompressed`, `danger_decompress`,
    `TransactionPayloadReader`: zstd C library); the derived impls.

    **Behaviour to note.** `len` is `header_size + payload.len()`, where `header_size` is only set
    by `deserialize`: for an event built with `new` it is 0, so `len` is the payload length alone,
    not the length `serialize` writes (`len_eq`, `len_new_bug`). `serialize` writes the stored
    `payload_size`, not the payload's length. `SIZE` is `ok none`, a `Result`, unlike the other
    events' `SIZE`: it is the hand-written model of `FunsExternal.lean` (Aeneas leaves the constant
    to us because `deserialize` is opaque), intended.
    **Upstream (not stated: `deserialize` is opaque here).** `deserialize` panics on server input:
    `TransactionPayloadCompressionType::try_from(val).unwrap()` for any unknown compression code
    (anything but 0 and 255), and on an unknown field type it reads the field length with the
    unchecked `eat_lenenc_int` and skips that many bytes with the unchecked `skip`
    (`transaction_payload_event.rs:317–318`), so a truncated or too-long unknown field panics. It
    does check the payload size against the buffer before using it.

    (Of these definitions, `txCompressionCode` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct TransactionPayloadEvent and its impls` -/

/-- `new(payload_size, algorithm, uncompressed_size, payload)`: those fields, `header_size` 0. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (ps : U64) (alg : binlog.consts.TransactionPayloadCompressionType) (us : U64) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.new into ps alg us p ⦃ e => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e = (ps.val, txCompressionCode alg, us.val, cowList c) ∧ e.header_size.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.new_spec`

/-- `with_payload_size`: replaces the stored payload size. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (ps : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size e ps = ok { e with payload_size := (ps, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size_spec`

/-- `with_algorithm`: replaces the compression type. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (alg : binlog.consts.TransactionPayloadCompressionType) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm e alg = ok { e with algorithm := alg }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm_spec`

/-- `with_uncompressed_size`: replaces the uncompressed size. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (us : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size e us = ok { e with uncompressed_size := (us, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size_spec`

/-- `with_payload`: replaces the payload (not the stored payload size). -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload into e p = ok { e with payload := (c, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_spec`

/-- `payload_size`: the stored payload size. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size e = ok e.payload_size.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size_eq`

/-- `payload_raw`: the payload. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw e ⦃ s => s.val = cowList e.payload.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw_spec`

/-- `algorithm`. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm e = ok e.algorithm

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm_eq`

/-- `uncompressed_size`. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size e = ok e.uncompressed_size.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size_eq`

/-- `into_owned`: the same fields (and `header_size`). -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned e ⦃ e' => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e' = (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e ∧ e'.header_size = e.header_size ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None` (a hand-written model, as `deserialize` is opaque). -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = ok none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MySerialize`: appends the layout `tpEnc`. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tpEnc e).length ≤ Usize.max) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tpEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `BinlogEvent::EVENT_TYPE`: `TRANSACTION_PAYLOAD_EVENT` (40). -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TRANSACTION_PAYLOAD_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: `header_size` (set only by `deserialize`; 0 after `new`) plus the payload length, capped. **Quirk:** for an event built with `new`, this is not the length `serialize` writes (`tpEnc`), which includes the header fields. -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (e.header_size.val + (cowList e.payload.1).length) evLenCap ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq`

/-- **Upstream bug:** for an event with `header_size` 0 (every event built with `new`), `len` is the capped payload length, strictly less than the length `serialize` writes (`tpEnc`, which has at least 7 header bytes). -/
recall binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_new_bug (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (h0 : e.header_size.val = 0) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (cowList e.payload.1).length evLenCap ∧ n.val + 7 ≤ (tpEnc e).length ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_new_bug`

end mysql_common
