import Defs

/-! Statements for `struct TransactionPayloadEvent and its impls` (spec file: `Specs/Binlog/Events/TransactionPayloadEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(payload_size, algorithm, uncompressed_size, payload)`: those fields, `header_size` 0. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (ps : U64) (alg : binlog.consts.TransactionPayloadCompressionType) (us : U64) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.new into ps alg us p ⦃ e => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e = (ps.val, txCompressionCode alg, us.val, cowList c) ∧ e.header_size.val = 0 ⦄ := by
  sorry

/-- `with_payload_size`: replaces the stored payload size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (ps : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size e ps = ok { e with payload_size := (ps, ()) } := by
  sorry

/-- `with_algorithm`: replaces the compression type. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (alg : binlog.consts.TransactionPayloadCompressionType) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm e alg = ok { e with algorithm := alg } := by
  sorry

/-- `with_uncompressed_size`: replaces the uncompressed size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (us : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size e us = ok { e with uncompressed_size := (us, ()) } := by
  sorry

/-- `with_payload`: replaces the payload (not the stored payload size). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload into e p = ok { e with payload := (c, ()) } := by
  sorry

/-- `payload_size`: the stored payload size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size e = ok e.payload_size.1 := by
  sorry

/-- `payload_raw`: the payload. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw e ⦃ s => s.val = cowList e.payload.1 ⦄ := by
  sorry

/-- `algorithm`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm e = ok e.algorithm := by
  sorry

/-- `uncompressed_size`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size e = ok e.uncompressed_size.1 := by
  sorry

/-- `into_owned`: the same fields (and `header_size`). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned e ⦃ e' => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e' = (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e ∧ e'.header_size = e.header_size ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None` (a hand-written model, as `deserialize` is opaque). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = ok none := by
  sorry

/-- `MySerialize`: appends the layout `tpEnc`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tpEnc e).length ≤ Usize.max) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tpEnc e ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `TRANSACTION_PAYLOAD_EVENT` (40). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TRANSACTION_PAYLOAD_EVENT := by
  sorry

/-- `BinlogStruct::len`: `header_size` (set only by `deserialize`; 0 after `new`) plus the payload length, capped. **Quirk:** for an event built with `new`, this is not the length `serialize` writes (`tpEnc`), which includes the header fields. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (e.header_size.val + (cowList e.payload.1).length) evLenCap ⦄ := by
  sorry

/-- **Upstream bug:** for an event with `header_size` 0 (every event built with `new`), `len` is the capped payload length, strictly less than the length `serialize` writes (`tpEnc`, which has at least 7 header bytes). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_new_bug (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (h0 : e.header_size.val = 0) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (cowList e.payload.1).length evLenCap ∧ n.val + 7 ≤ (tpEnc e).length ⦄ := by
  sorry

end mysql_common
