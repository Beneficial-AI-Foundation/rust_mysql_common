import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes

/-! Statements for `struct BeginLoadQueryEvent and its impls` (spec file: `Specs/Binlog/Events/BeginLoadQueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `new(file_id)`: that id and an empty block. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.new_spec (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.new fid ⦃ e => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e = (fid.val, []) ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.new
  step*

/-- `with_file_id`: replaces the id. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (fid : U32) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id e fid ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fid.val, cowList e.block_data.1) ⦄ := by
  obtain ⟨⟨a, pd⟩, b⟩ := e
  simp [binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_file_id]

/-- `with_block_data`: replaces the block. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (b : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into b = ok c) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data into e b ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (e.file_id.1.val, cowList c) ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.with_block_data
  step with PKUtil.rawbytes_new_spec _ into b c h as ⟨rb, hrb⟩
  simp [hrb]

/-- `file_id`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id_eq (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.file_id e = ok e.file_id.1 := by
  obtain ⟨⟨a, pd⟩, b⟩ := e
  rfl

/-- `block_data`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data e ⦃ s => s.val = cowList e.block_data.1 ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.impl.block_data
  exact PKUtil.eof_as_bytes_spec _

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned e ⦃ e' => (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e' = (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  simp [hrb]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; 4 bytes of id, the block as the rest. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) (if 4 ≤ buf.length then some ((leNat (buf.val.take 4), buf.val.drop 4), []) else none) r rest ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec as ⟨r, b1, h1⟩
  split_ifs at h1 ⊢ with hl
  · obtain ⟨h1, hb1⟩ := h1
    cases r with
    | Err e => simp at h1
    | Ok v =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with PKUtil.parse_eof_bytes_spec as ⟨r2, b2, h2, hb2⟩
      cases r2 with
      | Err e => simp at h2
      | Ok rb =>
        simp only [bind_ok]
        apply (WP.spec_ok _).mpr
        simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h1 h2
        simp [ReadsAs, h1, h2, hb1, hb2]
  · obtain ⟨h1, -⟩ := h1
    cases r with
    | Ok v => simp at h1
    | Err e =>
      simp [ReadsAs, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `MySerialize`: appends the layout `beginLoadQueryEnc`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (beginLoadQueryEnc e).length ≤ Usize.max) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ beginLoadQueryEnc e ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [misc.raw.int.RawInt.serialize_eq]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b1, hb1⟩
  · simp [beginLoadQueryEnc, alloc.vec.Vec.length] at h ⊢; omega
  apply WP.spec_mono (PKUtil.eof_ser _ b1 (by simp [beginLoadQueryEnc, alloc.vec.Vec.length, hb1] at h ⊢; omega))
  intro b hb
  simp [hb, hb1, beginLoadQueryEnc]

/-- Round trip. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = beginLoadQueryEnc e) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) = some ((fun (x : binlog.events.begin_load_query_event.BeginLoadQueryEvent) => (x.file_id.1.val, cowList x.block_data.1)) e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  have hl4 := PBUtil.length_leBytes 4 e.file_id.1.val
  have hlt : e.file_id.1.val < 2 ^ (8 * 4) := by scalar_tac
  have hlen : 4 ≤ buf.length := by simp [Slice.length, h, beginLoadQueryEnc, hl4]
  simp only [hlen, ite_true, ReadsAs] at hr
  obtain ⟨h1, h2⟩ := hr
  refine ⟨?_, h2⟩
  rw [h1, h, beginLoadQueryEnc, List.take_left' hl4, List.drop_left' hl4, leNat_leBytes_lt 4 _ hlt]

/-- `BinlogStruct::len`: the length of what `serialize` writes (`beginLoadQueryEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.begin_load_query_event.BeginLoadQueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (beginLoadQueryEnc e).length evLenCap ⦄ := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  have hM : (UScalar.cast .Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hUM : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  simp only [lift, bind_ok, hL]
  step with misc.raw.bytes.RawBytes.len_spec misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple _ rfl as ⟨i, hi⟩
  step*
  simp_all [sat_add_usize, beginLoadQueryEnc, evLenCap, misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec]
  have := PKUtil.cowList_length_le e.block_data.1
  omega

/-- `BinlogEvent::EVENT_TYPE`: `BEGIN_LOAD_QUERY_EVENT` (17). -/
theorem binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .BEGIN_LOAD_QUERY_EVENT := by
  unfold binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
