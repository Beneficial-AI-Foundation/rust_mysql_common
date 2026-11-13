import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Defs.LemmasBinlogEvents
import Proofs.Binlog.Events.QueryEvent.StatusVars
import Proofs.Misc.Raw.Skip
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent

/-! Statements for `struct QueryEvent and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `new(status_vars, schema)`: those, with their lengths (`min(len, 65535)`, `min(len, 255)`), everything else 0 or empty. -/
theorem binlog.events.query_event.QueryEvent.new_spec {T1 T2 : Type} (i1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (i2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (sv : T1) (sc : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h1 : i1.into sv = ok c1) (h2 : i2.into sc = ok c2) :
    binlog.events.query_event.QueryEvent.new i1 i2 sv sc ⦃ e => queryView e =
      { threadId := 0, execTime := 0, schemaLen := min (cowList c2).length 255, errorCode := 0,
        statusVarsLen := min (cowList c1).length 65535, statusVars := cowList c1, schema := cowList c2, query := [] } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.new
  step with PKUtil.rawbytes_new_spec _ i1 sv c1 h1 as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_new_spec _ i2 sc c2 h2 as ⟨rb2, hrb2⟩
  step*
  have e1 : (UScalar.cast .U8 i).val = min (cowList c2).length 255 := by
    rw [cast_u8_small i (by omega), i_post, hrb2]
  have e3 : (UScalar.cast .U16 i2).val = min (cowList c1).length 65535 := by
    rw [cast_u16_small i2 (by omega), i2_post, hrb]
  simp_all [queryView]

/-- `with_thread_id`. -/
theorem binlog.events.query_event.QueryEvent.with_thread_id_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_thread_id e x ⦃ e' => queryView e' = { queryView e with threadId := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_thread_id
  step*
  simp_all [queryView]

/-- `with_execution_time`. -/
theorem binlog.events.query_event.QueryEvent.with_execution_time_spec (e : binlog.events.query_event.QueryEvent) (x : U32) :
    binlog.events.query_event.QueryEvent.with_execution_time e x ⦃ e' => queryView e' = { queryView e with execTime := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_execution_time
  step*
  simp_all [queryView]

/-- `with_error_code`. -/
theorem binlog.events.query_event.QueryEvent.with_error_code_spec (e : binlog.events.query_event.QueryEvent) (x : U16) :
    binlog.events.query_event.QueryEvent.with_error_code e x ⦃ e' => queryView e' = { queryView e with errorCode := x.val } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_error_code
  step*
  simp_all [queryView]

/-- `with_status_vars`: the status variables and their length. -/
theorem binlog.events.query_event.QueryEvent.with_status_vars_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.query_event.QueryEvent.with_status_vars into e sv ⦃ e' => queryView e' = { queryView e with statusVars := cowList c, statusVarsLen := min (cowList c).length 65535 } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_status_vars
  obtain ⟨a, b, c0, d, ⟨x, pd⟩, sv0, sc0, sk, q0⟩ := e
  step with PKUtil.rawbytes_new_spec _ into sv c h as ⟨rb, hrb⟩
  step with bare_len_spec as ⟨i, hi⟩
  simp only [lift, bind_ok]
  apply (WP.spec_ok _).mpr
  rw [hrb] at hi
  simp [queryView, hrb, cast_u16_small i (by omega), hi]

/-- `with_schema`: the schema and its length. -/
theorem binlog.events.query_event.QueryEvent.with_schema_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (sc : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sc = ok c) :
    binlog.events.query_event.QueryEvent.with_schema into e sc ⦃ e' => queryView e' = { queryView e with schema := cowList c, schemaLen := min (cowList c).length 255 } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_schema
  obtain ⟨a, b, ⟨x, pd⟩, d, f, sv0, sc0, sk, q0⟩ := e
  step with PKUtil.rawbytes_new_spec _ into sc c h as ⟨rb, hrb⟩
  step with bare_len_spec as ⟨i, hi⟩
  simp only [lift, bind_ok]
  apply (WP.spec_ok _).mpr
  rw [hrb] at hi
  simp [queryView, hrb, cast_u8_small i (by omega), hi]

/-- `with_query`. -/
theorem binlog.events.query_event.QueryEvent.with_query_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.query_event.QueryEvent) (q : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into q = ok c) :
    binlog.events.query_event.QueryEvent.with_query into e q ⦃ e' => queryView e' = { queryView e with query := cowList c } ⦄ := by
  unfold binlog.events.query_event.QueryEvent.with_query
  step with PKUtil.rawbytes_new_spec _ into q c h as ⟨rb, hrb⟩
  simp [queryView, hrb]

/-- `thread_id`. -/
theorem binlog.events.query_event.QueryEvent.impl.thread_id_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.thread_id e = ok e.thread_id.1 := by
  obtain ⟨⟨_, _⟩, _⟩ := e; rfl

/-- `execution_time`. -/
theorem binlog.events.query_event.QueryEvent.impl.execution_time_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.execution_time e = ok e.execution_time.1 := by
  obtain ⟨_, ⟨_, _⟩, _⟩ := e; rfl

/-- `error_code`. -/
theorem binlog.events.query_event.QueryEvent.impl.error_code_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.error_code e = ok e.error_code.1 := by
  obtain ⟨_, _, _, ⟨_, _⟩, _⟩ := e; rfl

/-- `status_vars_raw`: the status variables, their first 65535 bytes. -/
theorem binlog.events.query_event.QueryEvent.status_vars_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.status_vars_raw e ⦃ s => s.val = (cowList e.status_vars.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.status_vars_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 65535#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `status_vars`: the status-variables block. -/
theorem binlog.events.query_event.QueryEvent.impl.status_vars_eq (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.impl.status_vars e = ok e.status_vars := by
  rfl

/-- `schema_raw`: the schema, its first 255 bytes. -/
theorem binlog.events.query_event.QueryEvent.schema_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.schema_raw e ⦃ s => s.val = (cowList e.schema.1).take 255 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.schema_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 255#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) _

/-- `query_raw`: the query. -/
theorem binlog.events.query_event.QueryEvent.query_raw_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.query_raw e ⦃ s => s.val = cowList e.query.1 ⦄ := by
  unfold binlog.events.query_event.QueryEvent.query_raw
  exact PKUtil.eof_as_bytes_spec _

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.query_event.QueryEvent.into_owned_spec (e : binlog.events.query_event.QueryEvent) :
    binlog.events.query_event.QueryEvent.into_owned e ⦃ e' => queryView e' = queryView e ⦄ := by
  unfold binlog.events.query_event.QueryEvent.into_owned binlog.events.query_event.StatusVars.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb1, hrb1⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb2, hrb2⟩
  simp [hrb, hrb1, hrb2, queryView]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

theorem parse_status_vars (len : U16) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16 buf len ⦃ r rest =>
      if len.val ≤ buf.length then ∃ v, r = .Ok v ∧ cowList v.1 = buf.val.take len.val ∧ rest.val = buf.val.drop len.val
      else okPart r = none ⦄ := by
  have hS : binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.SIZE = none := by
    unfold binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.SIZE; rfl
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [hS])]
  apply WP.spec_mono (binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec len buf)
  rintro ⟨r, rest⟩ hr
  split_ifs at hr ⊢
  · obtain ⟨h1, h2⟩ := hr
    cases r with
    | Ok v => exact ⟨v, rfl, by simpa using h1, h2⟩
    | Err e => simp at h1
  · exact hr.1

theorem parse_bare (M n : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize M)) buf n ⦃ r rest =>
      if n.val ≤ buf.length then ∃ v, r = .Ok v ∧ cowList v.1 = buf.val.take n.val ∧ rest.val = buf.val.drop n.val
      else okPart r = none ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq, misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq])]
  have h := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize M) n buf
    (fun o rest => if n.val ≤ buf.length then o = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none)
    (by
      apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec M n buf)
      rintro ⟨r, rest⟩ hr
      split_ifs at hr ⊢
      · exact hr
      · simp [hr.1])
  apply WP.spec_mono h
  rintro ⟨r, rest⟩ hr
  split_ifs at hr ⊢
  · obtain ⟨h1, h2⟩ := hr
    cases r with
    | Ok v => exact ⟨v, rfl, by simpa using h1, h2⟩
    | Err e => simp at h1
  · cases r with
    | Ok v => simp at hr
    | Err e => rfl

theorem parse_skip1 (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple 1#usize) buf () ⦃ r rest =>
      if 1 ≤ buf.length then ∃ v, r = .Ok v ∧ rest.val = buf.val.drop 1 else okPart r = none ⦄ := by
  have := IntAndMisc.parse_fixed (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple 1#usize) 1#usize
    (by simp [misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]) buf ()
    (fun o => o.isSome) (by
      intro sub hsub hl
      apply WP.spec_mono (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 1#usize sub
        (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      exact h1)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simp only [show (1#usize : Usize).val = 1 from rfl] at hr
  split_ifs at hr ⊢
  · obtain ⟨h1, h2⟩ := hr
    cases r with
    | Ok v => exact ⟨v, rfl, h2⟩
    | Err e => simp at h1
  · exact hr.1

theorem u8_sat_sub (x y : U8) : (core.num.U8.saturating_sub x y).val = x.val - y.val := by
  have hb : x.val - y.val < 2 ^ UScalarTy.U8.numBits := lt_of_le_of_lt (Nat.sub_le _ _) x.hBounds
  show (UScalar.saturating_sub x y).val = _
  simp only [UScalar.saturating_sub, Nat.zero_max]
  exact Nat.mod_eq_of_lt hb

theorem leNat_one (b : U8) : leNat [b] = b.val := by simp [leNat]

/-- `MyDeserialize`: total; `queryRead` with the FDE's query post-header length. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs queryView (queryRead (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT) buf.val) r rest ⦄ := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step with PKUtil.parse_usize_spec as ⟨r, b1, h1⟩
  by_cases hl : 13 ≤ buf.length
  · simp only [hl, ite_true] at h1
    obtain ⟨h1, hb1⟩ := h1
    have hlen : 13 ≤ buf.val.length := hl
    cases r with
    | Err e => simp at h1
    | Ok pb =>
      simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have lp : pb.val.length = 13 := by rw [h1]; simp; omega
      step with pu_leu32 as ⟨r1, s1, v1, hr1, h1v, hs1⟩
      subst hr1
      simp only [bind_ok]
      have l1 : s1.val.length = 9 := by rw [hs1]; simp [lp]
      step with pu_leu32 as ⟨r2, s2, v2, hr2, h2v, hs2⟩
      subst hr2
      simp only [bind_ok]
      have l2 : s2.val.length = 5 := by rw [hs2]; simp [l1]
      step with pu_u8 as ⟨r3, s3, v3, hr3, h3v, hs3⟩
      subst hr3
      simp only [bind_ok]
      have l3 : s3.val.length = 4 := by rw [hs3]; simp [l2]
      step with pu_leu16 as ⟨r4, s4, v4, hr4, h4v, hs4⟩
      subst hr4
      simp only [bind_ok]
      have l4 : s4.val.length = 2 := by rw [hs4]; simp [l3]
      step with pu_leu16 as ⟨r5, s5, v5, hr5, h5v, hs5⟩
      subst hr5
      simp only [bind_ok]
      have hET : binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .QUERY_EVENT := by
        unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl
      rw [hET]
      step with binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec as ⟨ph, hph⟩
      simp only [lift, bind_ok]
      have hsk : (UScalar.cast .Usize (core.num.U8.saturating_sub ph 13#u8)).val = postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT - 13 := by
        rw [IntAndMisc.cast_usize_small _ (by scalar_tac), u8_sat_sub, hph]; rfl
      have e2 : s2.val = pb.val.drop 8 := by rw [hs2, hs1, List.drop_drop]
      have e3 : s3.val = pb.val.drop 9 := by rw [hs3, e2, List.drop_drop]
      have e4 : s4.val = pb.val.drop 11 := by rw [hs4, e3, List.drop_drop]
      have f44 : leNat ((pb.val.drop 4).take 4) = v2.1.val := by rw [h2v, hs1]
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
      have f9 : leNat ((pb.val.drop 9).take 2) = v4.1.val := by rw [h4v, e3]
      have f11 : leNat ((pb.val.drop 11).take 2) = v5.1.val := by rw [h5v, e4]
      have hT13 : takeExact 13 buf.val = some (pb.val, b1.val) := by
        simp [takeExact, hlen, h1, hb1]
      step with io.ParseBuf.checked_skip_spec as ⟨bsk, b2, hsk2⟩
      rw [hsk] at hsk2
      split_ifs at hsk2 with hk
      · obtain ⟨rfl, hb2⟩ := hsk2
        have hTk : takeExact (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT - 13) b1.val = some (b1.val.take (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT - 13), b2.val) := by
          simp [takeExact, hb2]; simpa [Slice.length] using hk
        simp only [ite_true]
        step with IntAndMisc.rawint_deref_spec as ⟨d5, hd5⟩
        subst hd5
        step with parse_status_vars as ⟨r6, b3, h6⟩
        split_ifs at h6 with hk6
        · obtain ⟨sv, rfl, hsv, hb3⟩ := h6
          have hT6 : takeExact v5.1.val b2.val = some (b2.val.take v5.1.val, b3.val) := by
            simp [takeExact, hb3]; simpa [Slice.length] using hk6
          simp only [bind_ok]
          step with IntAndMisc.rawint_deref_spec as ⟨d3, hd3⟩
          subst hd3
          have hc3 : (UScalar.cast .Usize v3.1).val = v3.1.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
          step with parse_bare as ⟨r7, b4, h7⟩
          rw [hc3] at h7
          split_ifs at h7 with hk7
          · obtain ⟨rb, rfl, hrb, hb4⟩ := h7
            have hT7 : takeExact v3.1.val b3.val = some (b3.val.take v3.1.val, b4.val) := by
              simp [takeExact, hb4]; simpa [Slice.length] using hk7
            simp only [bind_ok]
            step with parse_skip1 as ⟨r8, b5, h8⟩
            split_ifs at h8 with hk8
            · obtain ⟨v8, rfl, hb5⟩ := h8
              have hT8 : takeExact 1 b4.val = some (b4.val.take 1, b5.val) := by
                simp only [takeExact, show 1 ≤ b4.val.length from by simpa [Slice.length] using hk8, ite_true, hb5]
              simp only [bind_ok]
              step with PKUtil.parse_eof_bytes_spec as ⟨r9, b6, h9, hb6⟩
              cases r9 with
              | Err e => simp at h9
              | Ok rb1 =>
                simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h9
                simp only [bind_ok]
                apply (WP.spec_ok _).mpr
                simp only [ReadsAs, queryRead, Option.bind_eq_bind, hT13, Option.bind_some, hTk, f11, hT6, f8, hT7, hT8]
                refine ⟨?_, hb6⟩
                simp [queryView, f44, f9, ← h1v, hsv, hrb, h9, hb5]
            · cases r8 with
              | Ok v => simp at h8
              | Err e =>
                have hT8 : takeExact 1 b4.val = none := by
                  simp [takeExact]; simpa [Slice.length] using hk8
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, queryRead, Option.bind_eq_bind, hT13, hTk, f11, hT6, f8', hT7, hT8]
          · cases r7 with
            | Ok v => simp at h7
            | Err e =>
              have hT7 : takeExact v3.1.val b3.val = none := by
                simp [takeExact]; simpa [Slice.length] using hk7
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, queryRead, Option.bind_eq_bind, hT13, hTk, f11, hT6, f8', hT7]
        · cases r6 with
          | Ok v => simp at h6
          | Err e =>
            have hT6 : takeExact v5.1.val b2.val = none := by
              simp [takeExact]; simpa [Slice.length] using hk6
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, queryRead, Option.bind_eq_bind, hT13, hTk, f11, hT6]
      · obtain ⟨rfl, -⟩ := hsk2
        have hTk : takeExact (postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT - 13) b1.val = none := by
          simp [takeExact]; simpa [Slice.length] using hk
        simp [ReadsAs, queryRead, Option.bind_eq_bind, hT13, hTk, misc.unexpected_buf_eof, misc.io_error_msg]
  · simp only [hl, ite_false] at h1
    obtain ⟨h1, -⟩ := h1
    have hfr : ¬ 13 ≤ buf.val.length := by simp [Slice.length] at hl; omega
    cases r with
    | Ok pb => simp at h1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, queryRead, takeExact, hfr]

/-- `MySerialize`: appends the layout `queryEnc`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.query_event.QueryEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (queryEnc e).length ≤ Usize.max) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ queryEnc e ⦄ := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize
  have hbl : buf.length = buf.val.length := rfl
  simp only [queryEnc, List.length_append, PBUtil.length_leBytes, List.length_take, List.length_cons,
    List.length_nil] at h
  simp only [misc.raw.int.RawInt.serialize_eq]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b1, hb1⟩
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b2, hb2⟩
  · simp only [alloc.vec.Vec.length, hb1, List.length_append, PBUtil.length_leBytes]; omega
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec as ⟨b3, hb3⟩
  · simp only [alloc.vec.Vec.length, hb2, hb1, List.length_append, PBUtil.length_leBytes]; omega
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b4, hb4⟩
  · simp only [alloc.vec.Vec.length, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil]; omega
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b5, hb5⟩
  · simp only [alloc.vec.Vec.length, hb4, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil]; omega
  step with binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b6, hb6⟩
  · simp only [alloc.vec.Vec.length, hb5, hb4, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes, List.length_cons, List.length_nil]; omega
  apply WP.spec_bind (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec _ e.schema b6
    (fun b => b.val = b6.val ++ (cowList e.schema.1).take 255) (fun sl hsl => by
      apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec 255#usize sl b6 (by
        simp only [Slice.length, hsl, alloc.vec.Vec.length, hb6, hb5, hb4, hb3, hb2, hb1, List.length_append,
          PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take]
        have : (255#usize : Usize).val = 255 := rfl
        omega))
      intro b hb; simp [hb, hsl]))
  intro b7 hb7
  step with misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b8, hb8⟩
  · simp only [alloc.vec.Vec.length, hb7, hb6, hb5, hb4, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes,
      List.length_cons, List.length_nil, List.length_take]; simp; omega
  apply WP.spec_mono (PKUtil.eof_ser _ b8 (by
    simp only [alloc.vec.Vec.length, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes,
      List.length_cons, List.length_nil, List.length_take, List.length_replicate]; simp; omega))
  intro b hb
  simp [hb, hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1, queryEnc]

/-- Round trip, for an event whose stored lengths are those of its status variables (at most 65535 bytes) and schema (at most 255), read with a query post-header of at most 13 bytes (`serialize` writes 13). -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.query_event.QueryEvent) (hsv : e.status_vars_len.1.val = (cowList e.status_vars.1).length)
    (hsv' : (cowList e.status_vars.1).length ≤ 65535) (hs : e.schema_len.1.val = (cowList e.schema.1).length)
    (hs' : (cowList e.schema.1).length ≤ 255) (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .QUERY_EVENT ≤ 13)
    (buf : io.ParseBuf) (h : buf.val = queryEnc e) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map queryView = some (queryView e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  rw [h, queryRead_queryEnc e _ hp hsv hsv' hs hs'] at hr
  simpa [ReadsAs] using hr

/-- `BinlogEvent::EVENT_TYPE`: `QUERY_EVENT` (2). -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .QUERY_EVENT := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

private theorem qlen_arith (A B C M : Nat) (hM : 2 ^ 32 - 1 ≤ M) :
    min (min M (min M (min M (min M (min M (min M (min M (min M (min M (0 + 4) + 4) + 1) + 2) + 2) +
      min (min A 65535) 65535) + min B 255) + 1) + C)) (2 ^ 32 - 1 - 19) =
    min (4 + 4 + (0 + 1) + 2 + 2 + min 65535 A + min 255 B + (0 + 1) + C) (2 ^ 32 - 1 - 19) := by
  omega

/-- `BinlogStruct::len`: the length of what `serialize` writes (`queryEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.query_event.QueryEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (queryEnc e).length evLenCap ⦄ := by
  unfold binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  have hM : (UScalar.cast .Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hM16 : (UScalar.cast .Usize core.num.U16.MAX).val = 65535 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hM8 : (UScalar.cast .Usize core.num.U8.MAX).val = 255 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hUM : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨a1, a2, a3, a4, a5, sv, ⟨c, u⟩, sk, ⟨c1, u1⟩⟩ := e
  simp only [lift, bind_ok, hL]
  step*
  have l1 := PKUtil.cowList_length_le sv.1
  have l2 := PKUtil.cowList_length_le c
  have l3 := PKUtil.cowList_length_le c1
  rw [n_post]
  simp only [sat_add_usize, hM, hM16, hM8, i2_post, i5_post, i8_post, i_post, Slice.len_val,
    queryEnc, evLenCap, List.length_append, PBUtil.length_leBytes, List.length_take, List.length_cons, List.length_nil]
  simp only [show (0#usize : Usize).val = 0 from rfl, show (4#usize : Usize).val = 4 from rfl,
    show (1#usize : Usize).val = 1 from rfl, show (2#usize : Usize).val = 2 from rfl, Slice.length]
  rw [s_post, s1_post]
  exact qlen_arith _ _ _ _ hUM

end mysql_common
