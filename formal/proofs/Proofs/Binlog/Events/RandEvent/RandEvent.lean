import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct RandEvent and its impls` (spec file: `Specs/Binlog/Events/RandEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `MyDeserialize::SIZE` is `some 16#usize`. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 16#usize := by
  unfold binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize` on at least 16 bytes: the two seeds. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) = some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  unfold binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  simp only [okPart, Option.map_some, Option.some.injEq, Prod.mk.injEq] at *
  subst_vars
  simp_all [List.drop_drop]

/-- `MyDeserialize` panics on fewer than 16 bytes. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 16) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic := by
  unfold binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  by_cases h8 : buf.length < 8
  · exact bind_fail_left (BinlogEvGtid.rawint_leu64_parse_unchecked_panics buf h8)
  · apply bind_fail_of_spec (BinlogEvGtid.rawint_leu64_parse_unchecked buf (by omega))
    rintro ⟨r, buf1⟩ ⟨x, rfl, -, hb⟩
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    exact bind_fail_left (BinlogEvGtid.rawint_leu64_parse_unchecked_panics buf1
      (by simp only [Slice.length, hb, List.length_drop] at *; omega))

/-- `buf.parse::<RandEvent>(ctx)`: total; an error on fewer than 16 bytes. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) (if 16 ≤ buf.length then some ((leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)), buf.val.drop 16) else none) r rest ⦄ := by
  have hs : proto.MyDeserialize.SIZE binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx = ok (some 16#usize) := by
    simp only [binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq]
  by_cases hl : 16 ≤ buf.length
  · simp only [ReadsAs, hl, ite_true]
    have := io.ParseBuf.parse_of_size _ buf ctx 16#usize hs hl
      (fun o => o.map (fun (x : binlog.events.rand_event.RandEvent) => (x.seed1.1.val, x.seed2.1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)))
    apply this
    intro sub hsub
    have hsl : 16 ≤ sub.length := by simp [Slice.length, hsub]; scalar_tac
    apply WP.spec_mono (deserialize_spec ctx sub hsl)
    rintro ⟨r, rest⟩ ⟨h1, -⟩
    simp only [WP.uncurry']
    rw [h1, hsub]
    simp [List.take_take, List.drop_take]
  · simp only [ReadsAs, hl, ite_false]
    apply WP.spec_mono (io.ParseBuf.parse_of_size_short _ buf ctx 16#usize hs (by scalar_tac))
    rintro ⟨r, rest⟩ ⟨h1, -⟩
    exact h1

/-- `MySerialize`: appends the layout `randEnc`. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rand_event.RandEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (randEnc e).length ≤ Usize.max) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ randEnc e ⦄ := by
  unfold binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [randEnc, List.length_append, length_leBytes] at h
  step*
  · simp [alloc.vec.Vec.length, buf1_post, length_leBytes]; omega
  · rwa [randEnc, ← List.append_assoc, ← buf1_post]

/-- Round trip. -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rand_event.RandEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = randEnc e ++ tail) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄ := by
  have hl : 16 ≤ buf.length := by simp [Slice.length, h, randEnc, length_leBytes]; omega
  apply WP.spec_mono (deserialize_spec ctx buf hl)
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  obtain ⟨x, rfl, hx⟩ := BinlogEvGtid.okPart_map_eq_some h1
  have hb8 : buf.val.take 8 = leBytes 8 e.seed1.1.val := by
    simp [h, randEnc, length_leBytes]
  have hb16 : (buf.val.drop 8).take 8 = leBytes 8 e.seed2.1.val := by
    simp [h, randEnc, length_leBytes]
  rw [hb8, hb16, BinlogEvGtid.leNat_leBytes_u64, BinlogEvGtid.leNat_leBytes_u64] at hx
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨a1, u1⟩, ⟨a2, u2⟩⟩ := x
    obtain ⟨⟨b1, v1⟩, ⟨b2, v2⟩⟩ := e
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [okPart, Option.some.injEq]
    have := UScalar.eq_of_val_eq hx1
    have := UScalar.eq_of_val_eq hx2
    subst_vars; rfl
  · rw [h2, h]; simp [randEnc, List.drop_append, length_leBytes]

/-- `BinlogEvent::EVENT_TYPE`: `RAND_EVENT` (13). -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .RAND_EVENT := by
  unfold binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- **Upstream bug:** `BinlogStruct::len` is 8, but the event data is 16 bytes (`randEnc`, two `u64`). -/
theorem binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.rand_event.RandEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 8#usize := by
  rfl

end mysql_common
