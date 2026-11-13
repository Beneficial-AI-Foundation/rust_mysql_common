import Defs
import Proofs.Util.BinlogEvGtid
import Proofs.Io.BufMutExt
import Proofs.Misc.LenencIntLen

/-! Statements for `struct TransactionPayloadEvent and its impls` (spec file: `Specs/Binlog/Events/TransactionPayloadEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

attribute [local step] io.BufMutExt.put_lenenc_int_spec misc.lenenc_int_len_spec

/-- `new(payload_size, algorithm, uncompressed_size, payload)`: those fields, `header_size` 0. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (ps : U64) (alg : binlog.consts.TransactionPayloadCompressionType) (us : U64) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.new into ps alg us p ⦃ e => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e = (ps.val, txCompressionCode alg, us.val, cowList c) ∧ e.header_size.val = 0 ⦄ := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.new; step*

/-- `with_payload_size`: replaces the stored payload size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (ps : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size e ps = ok { e with payload_size := (ps, ()) } := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_size; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `with_algorithm`: replaces the compression type. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (alg : binlog.consts.TransactionPayloadCompressionType) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm e alg = ok { e with algorithm := alg } := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.with_algorithm; rfl

/-- `with_uncompressed_size`: replaces the uncompressed size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (us : U64) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size e us = ok { e with uncompressed_size := (us, ()) } := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.with_uncompressed_size; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `with_payload`: replaces the payload (not the stored payload size). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (p : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into p = ok c) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload into e p = ok { e with payload := (c, ()) } := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.with_payload
  rw [misc.raw.bytes.RawBytes.new_eq _ _ _ _ h]
  exact bind_tc_ok _ _

/-- `payload_size`: the stored payload size. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size e = ok e.payload_size.1 := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.payload_size; rfl

/-- `payload_raw`: the payload. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw e ⦃ s => s.val = cowList e.payload.1 ⦄ := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.payload_raw; step*

/-- `algorithm`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm e = ok e.algorithm := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.algorithm; rfl

/-- `uncompressed_size`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size e = ok e.uncompressed_size.1 := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.impl.uncompressed_size; rfl

/-- `into_owned`: the same fields (and `header_size`). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned e ⦃ e' => (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e' = (fun (x : binlog.events.transaction_payload_event.TransactionPayloadEvent) => (x.payload_size.1.val, txCompressionCode x.algorithm, x.uncompressed_size.1.val, cowList x.payload.1)) e ∧ e'.header_size = e.header_size ⦄ := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned; step*

/-- `MyDeserialize::SIZE` is `None` (a hand-written model, as `deserialize` is opaque). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = ok none := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MySerialize`: appends the layout `tpEnc`. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tpEnc e).length ≤ Usize.max) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tpEnc e ⦄ := by
  obtain ⟨⟨ps, u1⟩, alg, ⟨us, u2⟩, pl, hs⟩ := e
  have := BinlogEvGtid.lenencInt_length_le
  cases alg <;>
  · unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize binlog.events.transaction_payload_event.serialize_uncompressed_size
      binlog.consts.TransactionPayloadCompressionType.Insts.CoreCmpPartialEqTransactionPayloadCompressionType.eq
    simp only [tpEnc, tpField, txCompressionCode, List.length_append] at h
    step*
    all_goals
      simp_all [alloc.vec.Vec.length, BinlogEvGtid.lenencInt_lenlen_length, read_discriminant,
        binlog.consts.TransactionPayloadCompressionType.read_discriminant, BinlogEvGtid.lenencInt_small_length, tpEnc, tpField,
        txCompressionCode]
    all_goals try omega
    all_goals try step*
    all_goals
      simp_all [alloc.vec.Vec.length, BinlogEvGtid.lenencInt_lenlen_length,
        BinlogEvGtid.lenencInt_small_length]
    all_goals try omega

/-- `BinlogEvent::EVENT_TYPE`: `TRANSACTION_PAYLOAD_EVENT` (40). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TRANSACTION_PAYLOAD_EVENT := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: `header_size` (set only by `deserialize`; 0 after `new`) plus the payload length, capped. **Quirk:** for an event built with `new`, this is not the length `serialize` writes (`tpEnc`), which includes the header fields. -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (e.header_size.val + (cowList e.payload.1).length) evLenCap ⦄ := by
  unfold binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  obtain ⟨ps, alg, us, ⟨c, u⟩, hs⟩ := e
  simp only
  step*
  · rw [i1_post]; simp [BinlogEvGtid.header_len_val]
  · have hs' : s.len.val = (cowList c).length := by simp [s_post]
    have hh := BinlogEvGtid.header_len_val
    simp only [n_post, len_post, i2_post, i1_post, hh, hs', evLenCap]
    rw [BinlogEvGtid.min_usize_cap]

/-- **Upstream bug:** for an event with `header_size` 0 (every event built with `new`), `len` is the capped payload length, strictly less than the length `serialize` writes (`tpEnc`, which has at least 7 header bytes). -/
theorem binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len_new_bug (e : binlog.events.transaction_payload_event.TransactionPayloadEvent) (h0 : e.header_size.val = 0) (v : binlog.consts.BinlogVersion) :
    binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (cowList e.payload.1).length evLenCap ∧ n.val + 7 ≤ (tpEnc e).length ⦄ := by
  apply WP.spec_mono (Insts.Mysql_commonBinlogBinlogStruct.len_eq e v)
  intro n hn
  rw [h0, Nat.zero_add] at hn
  refine ⟨hn, ?_⟩
  have h1 := BinlogEvGtid.lenencInt_length_pos
  have hle : n.val ≤ (cowList e.payload.1).length := by rw [hn]; exact Nat.min_le_left _ _
  simp only [tpEnc, tpField, List.length_append]
  have := h1 2; have := h1 1; have := h1 0; have := h1 (lenencInt (txCompressionCode e.algorithm)).length
  have := h1 (lenencInt e.payload_size.1.val).length; have := h1 (txCompressionCode e.algorithm); have := h1 e.payload_size.1.val
  omega

end mysql_common
