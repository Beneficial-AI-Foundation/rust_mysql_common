import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Binlog.Events.QueryEvent.QueryEvent
import Proofs.Misc.Raw.Const.Const

/-! Statements for `struct ExecuteLoadQueryEvent and its impls` (spec file: `Specs/Binlog/Events/ExecuteLoadQueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `new(file_id, dup_handling, status_vars, schema)`: those fields, the lengths set (`min(len, 65535)`, `min(len, 255)`), the rest 0 or empty. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (fid : U32) (d : binlog.consts.LoadDuplicateHandling) (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new i1 i2 fid d sv sc ⦃ e => elqView e =
      { q := { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
               statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1,
               schema := cowList c2, query := [] },
        fileId := fid.val, startPos := 0, endPos := 0, dup := loadDupCode d } ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.new
  step with PKUtil.rawbytes_new_spec _ i1 sv c1 h1 as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_new_spec _ i2 sc c2 h2 as ⟨rb2, hrb2⟩
  step*
  have e1 : (UScalar.cast .U8 i).val = min (cowList c2).length 255 := by
    rw [cast_u8_small i (by omega), i_post, hrb2]
  have e3 : (UScalar.cast .U16 i2).val = min (cowList c1).length 65535 := by
    rw [cast_u16_small i2 (by omega), i2_post, hrb]
  simp_all [elqView]

/-- `thread_id`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.thread_id e = ok e.thread_id.1 := by
  obtain ⟨⟨_, _⟩, _⟩ := e; rfl

/-- `execution_time`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.execution_time e = ok e.execution_time.1 := by
  obtain ⟨_, ⟨_, _⟩, _⟩ := e; rfl

/-- `error_code`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.error_code e = ok e.error_code.1 := by
  obtain ⟨_, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `file_id`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.file_id e = ok e.file_id.1 := by
  obtain ⟨_, _, _, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `start_pos`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.start_pos e = ok e.start_pos.1 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `end_pos`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.end_pos e = ok e.end_pos.1 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `dup_handling`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.dup_handling e = ok e.dup_handling.1 := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.status_vars_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 65535#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `status_vars`: the status-variables block. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars_eq (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.impl.status_vars e = ok e.status_vars := by
  rfl

/-- `schema_raw`: the schema, its first 255 bytes. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.schema_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 255#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `query_raw`: the query. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.query_raw
  exact PKUtil.eof_as_bytes_spec _

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned e ⦃ e' => elqView e' = elqView e ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned binlog.events.query_event.StatusVars.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb1, hrb1⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb2, hrb2⟩
  simp [hrb, hrb1, hrb2, elqView]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `elqRead`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs elqView (elqRead buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `elqEnc`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (elqEnc e).length ≤ Usize.max) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ elqEnc e ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize
  have hbl : buf.length = buf.val.length := rfl
  simp only [elqEnc, List.length_append, PBUtil.length_leBytes, List.length_take, List.length_cons,
    List.length_nil] at h
  simp only [misc.raw.int.RawInt.serialize_eq]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b1, hb1⟩
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b2, hb2⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb1]; omega
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec as ⟨b3, hb3⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb2, hb1]; omega
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b4, hb4⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb3, hb2, hb1]; omega
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b5, hb5⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb4, hb3, hb2, hb1]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b6, hb6⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb5, hb4, hb3, hb2, hb1]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b7, hb7⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb6, hb5, hb4, hb3, hb2, hb1]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b8, hb8⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb7, hb6, hb5, hb4, hb3, hb2, hb1]; omega
  have hp : (core.convert.IntoFrom U8.Insts.CoreConvertFromLoadDuplicateHandling).into e.dup_handling.1 =
      ok (UScalar.cast .U8 (read_discriminant e.dup_handling.1)) := rfl
  have hpv : UScalar.cast .U8 (read_discriminant e.dup_handling.1) = byte (loadDupCode e.dup_handling.1) := by
    cases e.dup_handling.1 <;> rfl
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ _ hp]
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec as ⟨b9, hb9⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]; omega
  step with binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b10, hb10⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]; omega
  apply WP.spec_bind (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec _ e.schema b10
    (fun b => b.val = b10.val ++ (cowList e.schema.1).take 255) (fun sl hsl => by
      apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec 255#usize sl b10 (by
        simp only [Slice.length, hsl, alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb10, hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]
        have : (255#usize : Usize).val = 255 := rfl
        omega))
      intro b hb; simp [hb, hsl]))
  intro b11 hb11
  step with misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b12, hb12⟩
  · simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, hb11, hb10, hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]; simp; omega
  apply WP.spec_mono (PKUtil.eof_ser _ b12 (by
    simp only [alloc.vec.Vec.length, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take, List.length_replicate, hb12, hb11, hb10, hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]; simp; omega))
  intro b hb
  simp [hb, hb12, hb11, hb10, hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1, elqEnc, hpv]

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = elqEnc e) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map elqView = some (elqView e) ∧ rest.val = [] ⦄ := by
  sorry

private theorem elq_len_arith (A B C M : Nat) (hM : 2 ^ 32 - 1 ≤ M) (hA : A ≤ 65522) :
    min (min M (min M (min M (min M (min M (min M (min M (min M (min M (min M (min M (min M (min M (0 + 4) + 4) + 1) + 2) + 2) + 4) + 4) + 4) + 1) +
      min (min A 65535) (65535 - 13)) + min B 255) + 1) + C)) (2 ^ 32 - 1 - 19) =
    min (4 + 4 + (0 + 1) + 2 + 2 + 4 + 4 + 4 + (0 + 1) + min 65535 A + min 255 B + (0 + 1) + C) (2 ^ 32 - 1 - 19) := by
  have h1 : min (min A 65535) (65535 - 13) = A := by omega
  have h2 : min 65535 A = A := by omega
  have hB : min B 255 ≤ 255 := Nat.min_le_right _ _
  have hk : ∀ x, x ≤ 70000 → min M x = x := fun x hx => by omega
  rw [h1, h2, Nat.min_comm 255 B]
  simp (disch := omega) only [hk]
  generalize min B 255 = B' at *
  omega

/-- `BinlogStruct::len`: the length `serialize` writes, capped, provided the status variables have at most 65522 bytes (beyond that `len` counts 65522 of them, `serialize` up to 65535). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (v : binlog.consts.BinlogVersion) (h : (cowList e.status_vars.1).length ≤ 65522) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (elqEnc e).length evLenCap ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  have hM : (UScalar.cast .Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hM16 : (UScalar.cast .Usize core.num.U16.MAX).val = 65535 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hM8 : (UScalar.cast .Usize core.num.U8.MAX).val = 255 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hUM : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, sv, ⟨c, u⟩, sk, ⟨c1, u1⟩⟩ := e
  simp only [lift, bind_ok, hL]
  step*
  rw [n_post]
  simp only [sat_add_usize, hM, hM16, hM8, i3_post, i6_post, i9_post, i_post, i2_post, Slice.len_val,
    elqEnc, evLenCap, List.length_append, PBUtil.length_leBytes, List.length_take, List.length_cons, List.length_nil]
  simp only [show (0#usize : Usize).val = 0 from rfl, show (4#usize : Usize).val = 4 from rfl,
    show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, Slice.length]
  rw [s_post, s1_post]
  simp only at h
  exact elq_len_arith _ _ _ _ hUM h

/-- `BinlogEvent::EVENT_TYPE`: `EXECUTE_LOAD_QUERY_EVENT` (18). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .EXECUTE_LOAD_QUERY_EVENT := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
