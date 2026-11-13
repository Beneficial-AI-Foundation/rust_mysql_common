import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Binlog.Events.QueryEvent.QueryEvent
import Proofs.Misc.Raw.Const.Const
import Proofs.Binlog.Consts.LoadDuplicateHandling

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

private theorem pu_load_dup (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling
      binlog.consts.UnknownDuplicateHandling.Insts.CoreErrorError) buf () ⦃ r _rest =>
      (okPart r).map (·.1) = loadDupOfCode (leNat (buf.val.take 1)) ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    U8.Insts.Mysql_commonMiscRawIntIntReprU8
    binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling
    binlog.consts.UnknownDuplicateHandling.Insts.CoreErrorError buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1)
    (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h)
    (fun p o => o = loadDupOfCode p.val)
    (fun p => by
      have hh := binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from_spec p
      simp only [hh]
      apply (WP.spec_ok _).mpr
      split <;> simp_all [okPart])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨ho, -⟩, hm⟩
  cases o with
  | none => simp at ho
  | some p =>
    simp only [Option.map_some, Option.some.injEq] at ho hm
    simpa [← ho] using hm

private theorem loadDup_some (n : Nat) (x : binlog.consts.LoadDuplicateHandling) (h : loadDupOfCode n = some x) :
    loadDupCode x = n ∧ n ≤ 2 := by
  unfold loadDupOfCode at h
  have := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp at this hm
  rcases hm with rfl | rfl | rfl <;> simp_all [loadDupCode]

private theorem loadDup_none (n : Nat) (h : loadDupOfCode n = none) : 2 < n := by
  unfold loadDupOfCode at h
  simp [List.find?_eq_none, loadDupCode] at h
  omega

/-- `MyDeserialize`: total; `elqRead`. -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs elqView (elqRead buf.val) r rest ⦄ := by
  unfold binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step with PKUtil.parse_usize_spec as ⟨r, b1, h1⟩
  by_cases hl : 26 ≤ buf.length
  · simp only [hl, ite_true] at h1
    obtain ⟨h1, hb1⟩ := h1
    have hlen : 26 ≤ buf.val.length := hl
    cases r with
    | Err e => simp at h1
    | Ok pb =>
      simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have lp : pb.val.length = 26 := by rw [h1]; simp; omega
      step with pu_leu32 as ⟨r1, s1, v1, hr1, h1v, hs1⟩
      subst hr1
      simp only [bind_ok]
      have l1 : s1.val.length = 22 := by rw [hs1]; simp [lp]
      step with pu_leu32 as ⟨r2, s2, v2, hr2, h2v, hs2⟩
      subst hr2
      simp only [bind_ok]
      have l2 : s2.val.length = 18 := by rw [hs2]; simp [l1]
      step with pu_u8 as ⟨r3, s3, v3, hr3, h3v, hs3⟩
      subst hr3
      simp only [bind_ok]
      have l3 : s3.val.length = 17 := by rw [hs3]; simp [l2]
      step with pu_leu16 as ⟨r4, s4, v4, hr4, h4v, hs4⟩
      subst hr4
      simp only [bind_ok]
      have l4 : s4.val.length = 15 := by rw [hs4]; simp [l3]
      step with pu_leu16 as ⟨r5, s5, v5, hr5, h5v, hs5⟩
      subst hr5
      simp only [bind_ok]
      have l5 : s5.val.length = 13 := by rw [hs5]; simp [l4]
      step with pu_leu32 as ⟨r6, s6, v6, hr6, h6v, hs6⟩
      subst hr6
      simp only [bind_ok]
      have l6 : s6.val.length = 9 := by rw [hs6]; simp [l5]
      step with pu_leu32 as ⟨r7, s7, v7, hr7, h7v, hs7⟩
      subst hr7
      simp only [bind_ok]
      have l7 : s7.val.length = 5 := by rw [hs7]; simp [l6]
      step with pu_leu32 as ⟨r8, s8, v8, hr8, h8v, hs8⟩
      subst hr8
      simp only [bind_ok]
      have l8 : s8.val.length = 1 := by rw [hs8]; simp [l7]
      step with pu_load_dup as ⟨r9, s9, h9v⟩
      have e2 : s2.val = pb.val.drop 8 := by rw [hs2, hs1, List.drop_drop]
      have e3 : s3.val = pb.val.drop 9 := by rw [hs3, e2, List.drop_drop]
      have e4 : s4.val = pb.val.drop 11 := by rw [hs4, e3, List.drop_drop]
      have e5 : s5.val = pb.val.drop 13 := by rw [hs5, e4, List.drop_drop]
      have e6 : s6.val = pb.val.drop 17 := by rw [hs6, e5, List.drop_drop]
      have e7 : s7.val = pb.val.drop 21 := by rw [hs7, e6, List.drop_drop]
      have e8 : s8.val = pb.val.drop 25 := by rw [hs8, e7, List.drop_drop]
      have f8 : (pb.val.drop 8).headD (byte 0) = v3.1 := by
        rw [← e2]
        obtain ⟨b, t, hbt⟩ : ∃ b t, s2.val = b :: t := by
          cases hx : s2.val with
          | nil => rw [hx] at l2; simp at l2
          | cons b t => exact ⟨b, t, rfl⟩
        rw [hbt] at h3v ⊢
        apply UScalar.eq_of_val_eq
        simp [h3v, leNat]
      have f8' : pb.val[8]?.getD (byte 0) = v3.1 := by rw [← f8]; simp
      have f25 : ((pb.val.drop 25).headD (byte 0)).val = leNat (s8.val.take 1) := by
        rw [← e8]
        obtain ⟨b, t, hbt⟩ : ∃ b t, s8.val = b :: t := by
          cases hx : s8.val with
          | nil => rw [hx] at l8; simp at l8
          | cons b t => exact ⟨b, t, rfl⟩
        rw [hbt]; simp [leNat]
      have f25' : (pb.val[25]?.getD (byte 0)).val = leNat (s8.val.take 1) := by rw [← f25]; simp
      have f44 : leNat ((pb.val.drop 4).take 4) = v2.1.val := by rw [h2v, hs1]
      have f9 : leNat ((pb.val.drop 9).take 2) = v4.1.val := by rw [h4v, e3]
      have f11 : leNat ((pb.val.drop 11).take 2) = v5.1.val := by rw [h5v, e4]
      have f13 : leNat ((pb.val.drop 13).take 4) = v6.1.val := by rw [h6v, e5]
      have f17 : leNat ((pb.val.drop 17).take 4) = v7.1.val := by rw [h7v, e6]
      have f21 : leNat ((pb.val.drop 21).take 4) = v8.1.val := by rw [h8v, e7]
      have hT26 : takeExact 26 buf.val = some (pb.val, b1.val) := by
        simp [takeExact, hlen, h1, hb1]
      cases r9 with
      | Err e =>
        simp only [PKUtil.okPart_Err, Option.map_none] at h9v
        have hd := loadDup_none _ h9v.symm
        rw [← f25'] at hd
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, elqRead, Option.bind_eq_bind, hT26, hd]
      | Ok v9 =>
        simp only [PKUtil.okPart_Ok, Option.map_some] at h9v
        obtain ⟨hdc, hd2⟩ := loadDup_some _ _ h9v.symm
        rw [← f25'] at hdc hd2
        have hnd : ¬ 2 < (pb.val[25]?.getD (byte 0)).val := by omega
        have hgd : (pb.val.drop 25).headD (byte 0) = pb.val[25]?.getD (byte 0) := by simp
        have hnd' : ¬ 2 < ((pb.val.drop 25).headD (byte 0)).val := by rw [hgd]; exact hnd
        simp only [bind_ok]
        step with IntAndMisc.rawint_deref_spec as ⟨d5, hd5⟩
        subst hd5
        step with parse_status_vars as ⟨r10, b2, h10⟩
        split_ifs at h10 with hk10
        · obtain ⟨sv, rfl, hsv, hb2⟩ := h10
          have hT10 : takeExact v5.1.val b1.val = some (b1.val.take v5.1.val, b2.val) := by
            simp [takeExact, hb2]; simpa [Slice.length] using hk10
          simp only [bind_ok]
          step with IntAndMisc.rawint_deref_spec as ⟨d3, hd3⟩
          subst hd3
          have hc3 : (UScalar.cast .Usize v3.1).val = v3.1.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
          simp only [lift, bind_ok]
          step with parse_bare as ⟨r11, b3, h11⟩
          rw [hc3] at h11
          split_ifs at h11 with hk11
          · obtain ⟨rb, rfl, hrb, hb3⟩ := h11
            have hT11 : takeExact v3.1.val b2.val = some (b2.val.take v3.1.val, b3.val) := by
              simp [takeExact, hb3]; simpa [Slice.length] using hk11
            simp only [bind_ok]
            step with parse_skip1 as ⟨r12, b4, h12⟩
            split_ifs at h12 with hk12
            · obtain ⟨v12, rfl, hb4⟩ := h12
              have hT12 : takeExact 1 b3.val = some (b3.val.take 1, b4.val) := by
                simp only [takeExact, show 1 ≤ b3.val.length from by simpa [Slice.length] using hk12, ite_true, hb4]
              simp only [bind_ok]
              step with PKUtil.parse_eof_bytes_spec as ⟨r13, b5, h13, hb5⟩
              cases r13 with
              | Err e => simp at h13
              | Ok rb1 =>
                simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h13
                simp only [bind_ok]
                apply (WP.spec_ok _).mpr
                simp only [ReadsAs, elqRead, Option.bind_eq_bind, hT26, Option.bind_some, f11, hT10, f8, hT11, hT12, hnd', ite_false]
                refine ⟨?_, hb5⟩
                simp [elqView, f44, f9, f13, f17, f21, ← h1v, hsv, hrb, h13, hb4, hdc]
            · cases r12 with
              | Ok v => simp at h12
              | Err e =>
                have hT12 : takeExact 1 b3.val = none := by
                  simp [takeExact]; simpa [Slice.length] using hk12
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, elqRead, Option.bind_eq_bind, hT26, hnd, f11, hT10, f8', hT11, hT12]
          · cases r11 with
            | Ok v => simp at h11
            | Err e =>
              have hT11 : takeExact v3.1.val b2.val = none := by
                simp [takeExact]; simpa [Slice.length] using hk11
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, elqRead, Option.bind_eq_bind, hT26, hnd, f11, hT10, f8', hT11]
        · cases r10 with
          | Ok v => simp at h10
          | Err e =>
            have hT10 : takeExact v5.1.val b1.val = none := by
              simp [takeExact]; simpa [Slice.length] using hk10
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, elqRead, Option.bind_eq_bind, hT26, hnd, f11, hT10]
  · simp only [hl, ite_false] at h1
    obtain ⟨h1, -⟩ := h1
    have hfr : ¬ 26 ≤ buf.val.length := by simp [Slice.length] at hl; omega
    cases r with
    | Ok pb => simp at h1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, elqRead, takeExact, hfr]

set_option linter.unusedSimpArgs false in
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

private theorem elqRead_elqEnc (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent)
    (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length) (hsv' : (cowList e.status_vars.1).length ≤ 65535)
    (hs : e.schema_len.1.val = (cowList e.schema.1).length) (hs' : (cowList e.schema.1).length ≤ 255) :
    elqRead (elqEnc e) = some (elqView e, []) := by
  have hsvt : (cowList e.status_vars.1).take 65535 = cowList e.status_vars.1 := List.take_of_length_le hsv'
  have hsct : (cowList e.schema.1).take 255 = cowList e.schema.1 := List.take_of_length_le hs'
  have a1 := PBUtil.length_leBytes 4 e.thread_id.1.val
  have a2 := PBUtil.length_leBytes 4 e.execution_time.1.val
  have a3 := PBUtil.length_leBytes 2 e.error_code.1.val
  have a4 := PBUtil.length_leBytes 2 e.status_vars_len.1.val
  have a5 := PBUtil.length_leBytes 4 e.file_id.1.val
  have a6 := PBUtil.length_leBytes 4 e.start_pos.1.val
  have a7 := PBUtil.length_leBytes 4 e.end_pos.1.val
  have b1 : e.thread_id.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b2 : e.execution_time.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b3 : e.error_code.1.val < 2 ^ (8 * 2) := by scalar_tac
  have b4 : e.status_vars_len.1.val < 2 ^ (8 * 2) := by scalar_tac
  have b5 : e.file_id.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b6 : e.start_pos.1.val < 2 ^ (8 * 4) := by scalar_tac
  have b7 : e.end_pos.1.val < 2 ^ (8 * 4) := by scalar_tac
  have hd : (byte (loadDupCode e.dup_handling.1)).val = loadDupCode e.dup_handling.1 := by
    cases e.dup_handling.1 <;> rfl
  have hd2 : loadDupCode e.dup_handling.1 ≤ 2 := by cases e.dup_handling.1 <;> simp [loadDupCode]
  set H := leBytes 4 e.thread_id.1.val ++ leBytes 4 e.execution_time.1.val ++ [e.schema_len.1] ++
    leBytes 2 e.error_code.1.val ++ leBytes 2 e.status_vars_len.1.val ++ leBytes 4 e.file_id.1.val ++
    leBytes 4 e.start_pos.1.val ++ leBytes 4 e.end_pos.1.val ++ [byte (loadDupCode e.dup_handling.1)] with hH
  have hHl : H.length = 26 := by simp [hH, a1, a2, a3, a4, a5, a6, a7]
  have hq : elqEnc e = H ++ (cowList e.status_vars.1 ++ (cowList e.schema.1 ++ ([byte 0] ++ cowList e.query.1))) := by
    simp only [elqEnc, hsvt, hsct, hH, List.append_assoc]
  have t4 : H.take 4 = leBytes 4 e.thread_id.1.val := by simp [hH, a1]
  have t44 : (H.drop 4).take 4 = leBytes 4 e.execution_time.1.val := by simp [hH, a1, a2]
  have t8 : (H.drop 8).headD (byte 0) = e.schema_len.1 := by simp [hH, List.drop_append, a1, a2]
  have t92 : (H.drop 9).take 2 = leBytes 2 e.error_code.1.val := by simp [hH, List.drop_append, a1, a2, a3]
  have t112 : (H.drop 11).take 2 = leBytes 2 e.status_vars_len.1.val := by simp [hH, List.drop_append, a1, a2, a3, a4]
  have t13 : (H.drop 13).take 4 = leBytes 4 e.file_id.1.val := by simp [hH, List.drop_append, a1, a2, a3, a4, a5]
  have t17 : (H.drop 17).take 4 = leBytes 4 e.start_pos.1.val := by simp [hH, List.drop_append, a1, a2, a3, a4, a5, a6]
  have t21 : (H.drop 21).take 4 = leBytes 4 e.end_pos.1.val := by simp [hH, List.drop_append, a1, a2, a3, a4, a5, a6, a7]
  have t25 : (H.drop 25).headD (byte 0) = byte (loadDupCode e.dup_handling.1) := by
    simp [hH, List.drop_append, a1, a2, a3, a4, a5, a6, a7]
  rw [hq]
  simp only [elqRead, Option.bind_eq_bind]
  rw [takeExact_app _ _ 26 hHl]
  simp only [Option.bind_some, t112, t8, t4, t44, t92, t13, t17, t21, t25, hd]
  simp only [leNat_leBytes_lt 2 _ b4, leNat_leBytes_lt 2 _ b3, leNat_leBytes_lt 4 _ b1,
    leNat_leBytes_lt 4 _ b2, leNat_leBytes_lt 4 _ b5, leNat_leBytes_lt 4 _ b6, leNat_leBytes_lt 4 _ b7]
  rw [hsv, takeExact_app _ _ _ rfl]
  simp only [Option.bind_some]
  rw [hs, takeExact_app _ _ _ rfl]
  simp only [Option.bind_some]
  rw [takeExact_app [byte 0] _ 1 rfl]
  simp only [Option.bind_some, elqView, hsv, hs, show ¬ 2 < loadDupCode e.dup_handling.1 from by omega, ite_false]

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255). -/
theorem binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.execute_load_query_event.ExecuteLoadQueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = elqEnc e) :
    binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map elqView = some (elqView e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  rw [h, elqRead_elqEnc e hsv hsv' hs hs'] at hr
  simpa [ReadsAs] using hr

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
