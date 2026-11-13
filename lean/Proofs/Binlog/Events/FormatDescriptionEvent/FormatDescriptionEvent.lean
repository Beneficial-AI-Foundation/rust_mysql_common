import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.FixedLengthText
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Const.Const
import Proofs.Binlog.Consts.BinlogVersion
import Proofs.Binlog.Events.Mod.BinlogEventFooter
import Proofs.Defs.LemmasBinlogEvents

/-! Statements for `struct FormatDescriptionEvent and its impls` (spec file: `Specs/Binlog/Events/FormatDescriptionEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `SERVER_VER_LEN`: 50. -/
theorem binlog.events.format_description_event.SERVER_VER_LEN_eq :
    binlog.events.format_description_event.SERVER_VER_LEN = 50#usize := by
  unfold binlog.events.format_description_event.SERVER_VER_LEN; rfl

/-- `new(version)`: that version, an empty server version and post-header array, timestamp 0, the default footer. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.new_spec (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.new v ⦃ e => fdeView e = { version := v, serverVersion := [], createTimestamp := 0, lens := [] } ∧
      footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.new
  step*
  step with binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default_spec as ⟨bef, hb1, hb2⟩
  simp_all [fdeView, fdeLens]

/-- `with_binlog_version`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version e v ⦃ e' => fdeView e' = { fdeView e with version := v } ∧ e'.footer = e.footer ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version
  step*
  simp_all [fdeView, fdeLens]

/-- `with_server_version` (stored as given; padded or truncated to 50 bytes only when written). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_server_version_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_server_version into e sv ⦃ e' => fdeView e' = { fdeView e with serverVersion := cowList c } ∧ e'.footer = e.footer ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.with_server_version
  step with PKUtil.rawbytes_new_spec _ into sv c h as ⟨rb, hrb⟩
  simp [hrb, fdeView, fdeLens]

/-- `with_create_timestamp`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (ts : U32) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp e ts ⦃ e' => fdeView e' = { fdeView e with createTimestamp := ts.val } ∧ e'.footer = e.footer ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp
  step*
  simp_all [fdeView, fdeLens]

/-- `with_event_type_header_lengths`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (ls : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into ls = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths into e ls ⦃ e' => fdeView e' = { fdeView e with lens := cowList c } ∧ e'.footer = e.footer ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths
  step with PKUtil.rawbytes_new_spec _ into ls c h as ⟨rb, hrb⟩
  simp [hrb, fdeView, fdeLens]

/-- `with_footer`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) (f : binlog.events.BinlogEventFooter) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_footer e f = ok { e with footer := f } := by
  rfl

/-- `binlog_version`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version e = ok e.binlog_version.1 := by
  obtain ⟨⟨a, b⟩, _⟩ := e; rfl

/-- `server_version_raw`: the stored server version, its first 50 bytes. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw e ⦃ s => s.val = (cowList e.server_version.1).take 50 ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw
  exact misc.raw.bytes.RawBytes.as_bytes_spec _ 50#usize
    (by simp [misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec]) _

/-- `create_timestamp`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp e = ok e.create_timestamp.1 := by
  obtain ⟨_, _, ⟨a, b⟩, _⟩ := e; rfl

/-- `event_header_length`: always 19. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length e = ok 19#u8 := by
  rfl

/-- `event_type_header_lengths`: the post-header lengths array. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths e ⦃ s => s.val = fdeLens e ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths
  exact PKUtil.eof_as_bytes_spec _

/-- `footer`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.footer e = ok e.footer := by
  rfl

/-- `get_event_type_header_length(t)`: `postHeaderLen` (0 for `UNKNOWN_EVENT`; else the array entry `t - 1`, or the default if the array is shorter). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (t : binlog.consts.EventType) :
    binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length e t ⦃ n => n.val = postHeaderLen (fdeLens e) t ⦄ := by
  sorry

/-- `into_owned`: the same fields and footer. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.into_owned_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.into_owned e ⦃ e' => fdeView e' = fdeView e ∧ e'.footer = e.footer ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb1, hrb1⟩
  simp [hrb, hrb1, fdeView, fdeLens]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `fdeRead` (a known version, header length 19, the rest as the post-header lengths); the footer is the default. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs fdeView (fdeRead buf.val) r rest ∧
      ∀ e, okPart r = some e → footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step with PKUtil.parse_usize_spec as ⟨r, b1, h1⟩
  by_cases hl : 57 ≤ buf.length
  · simp only [hl, ite_true] at h1
    obtain ⟨h1, hb1⟩ := h1
    have hlen : 57 ≤ buf.val.length := hl
    have hfr : ¬ buf.val.length < 57 := by omega
    cases r with
    | Err e => simp at h1
    | Ok pb =>
      simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have lp : pb.val.length = 57 := by rw [h1]; simp; omega
      step with pu_binlog_version as ⟨r1, s1, hv, hs1⟩
      have t2 : pb.val.take 2 = buf.val.take 2 := by rw [h1, List.take_take]; rfl
      rw [t2] at hv
      cases r1 with
      | Err e =>
        simp only [PKUtil.okPart_Err, Option.map_none] at hv
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, fdeRead, hfr, ← hv]
      | Ok val =>
        simp only [PKUtil.okPart_Ok, Option.map_some] at hv
        simp only [bind_ok]
        have ls1 : s1.val.length = 55 := by rw [hs1]; simp [lp]
        step with pu_fixed_text as ⟨r2, s2, rb, hr2, hrb, hs2⟩
        subst hr2
        simp only [bind_ok]
        have ls2 : s2.val.length = 5 := by rw [hs2]; simp [ls1]
        step with pu_leu32 as ⟨r3, s3, v3, hr3, h3, hs3⟩
        subst hr3
        simp only [bind_ok]
        have ls3 : s3.val.length = 1 := by rw [hs3]; simp [ls2]
        step with pu_constu8 19#u8 binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreErrorError binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreDefaultDefault (by simp [binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreDefaultDefault.default]) as ⟨r4, s4, h4, hs4⟩
        have e1 : s1.val = (buf.val.drop 2).take 55 := by rw [hs1, h1, List.drop_take]
        have e2 : s2.val = (buf.val.drop 52).take 5 := by rw [hs2, e1, List.drop_take, List.drop_drop]
        have e3 : s3.val = (buf.val.drop 56).take 1 := by rw [hs3, e2, List.drop_take, List.drop_drop]
        have hsv : cowList rb.1 = (buf.val.drop 2).take 50 := by rw [hrb, e1, List.take_take]; simp
        have hts : v3.1.val = leNat ((buf.val.drop 52).take 4) := by rw [h3, e2, List.take_take]; simp
        have h56 : leNat (s3.val.take 1) = (buf.val[56]?.map (·.val)).getD 0 := by
          rw [e3]
          rw [List.take_take, show min 1 1 = 1 from rfl]
          rw [List.take_one, List.head?_drop]
          cases buf.val[56]? <;> simp [leNat]
        have hsome : ∃ b, buf.val[56]? = some b := ⟨buf.val[56]'(by omega), List.getElem?_eq_getElem _⟩
        obtain ⟨b56, hb56⟩ := hsome
        rw [hb56] at h56
        simp only [Option.map_some, Option.getD_some] at h56
        cases r4 with
        | Err e =>
          have hne : ¬ b56.val = 19 := by rw [← h56]; simpa using h4
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, fdeRead, hfr, ← hv, hb56, hne]
        | Ok val2 =>
          have heq : b56.val = 19 := by rw [← h56]; simpa using h4
          simp only [bind_ok]
          step with PKUtil.parse_eof_bytes_spec as ⟨r5, b2, h5, hb2⟩
          cases r5 with
          | Err e => simp at h5
          | Ok rb1 =>
            simp only [PKUtil.okPart_Ok, Option.map_some, Option.some.injEq] at h5
            simp only [bind_ok]
            step with binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default_spec as ⟨bef, hf1, hf2⟩
            refine ⟨?_, ?_⟩
            · simp only [ReadsAs, fdeRead, hfr, ite_false, ← hv, hb56, Option.map_some, heq, ne_eq, not_true_eq_false]
              refine ⟨?_, hb2⟩
              simp only [PKUtil.okPart_Ok, Option.map_some, fdeView, fdeLens, hsv, hts, h5, hb1]
            · intro e he
              simp only [PKUtil.okPart_Ok, Option.some.injEq] at he
              subst he
              exact ⟨hf1, hf2⟩
  · simp only [hl, ite_false] at h1
    obtain ⟨h1, -⟩ := h1
    have hfr : buf.val.length < 57 := by simp [Slice.length] at hl; omega
    cases r with
    | Ok pb => simp at h1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ReadsAs, fdeRead, hfr]

/-- `MySerialize`: appends the layout `fdeEnc`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (fdeEnc e).length ≤ Usize.max) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ fdeEnc e ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize
  have hp : (core.convert.IntoFrom U16.Insts.CoreConvertFromBinlogVersion).into e.binlog_version.1 =
      ok (UScalar.cast .U16 (read_discriminant e.binlog_version.1)) := rfl
  have hpv : (UScalar.cast .U16 (read_discriminant e.binlog_version.1)).val = binlogVersionCode e.binlog_version.1 := by
    cases e.binlog_version.1 <;> rfl
  have hfl := fixedText_length 50 (cowList e.server_version.1)
  simp only [fdeEnc, fdeLens, List.length_append, PBUtil.length_leBytes, hfl, List.length_cons, List.length_nil] at h
  have hbl : buf.length = buf.val.length := rfl
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ _ hp]
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b1, hb1⟩
  apply WP.spec_bind (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec _ e.server_version b1
    (fun b => b.val = b1.val ++ fixedText 50 (cowList e.server_version.1)) (fun s hs => by
      apply WP.spec_mono (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec 50#usize s b1
        (by simp only [alloc.vec.Vec.length, hb1, List.length_append, PBUtil.length_leBytes]; scalar_tac))
      intro b hb
      rw [hb]
      simp [hs, Slice.length, fixedText]))
  intro b2 hb2
  simp only [misc.raw.int.RawInt.serialize_eq]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b3, hb3⟩
  · simp only [alloc.vec.Vec.length, hb2, hb1, List.length_append, PBUtil.length_leBytes, hfl]; omega
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b4, hb4⟩
  · simp only [alloc.vec.Vec.length, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes, hfl]; omega
  apply WP.spec_mono (PKUtil.eof_ser _ b4 (by
    simp only [alloc.vec.Vec.length, hb4, hb3, hb2, hb1, List.length_append, PBUtil.length_leBytes, hfl,
      List.length_cons, List.length_nil]; omega))
  intro b hb
  rw [hb, hb4, hb3, hb2, hb1, hpv]
  simp only [fdeEnc, fdeLens, List.append_assoc]
  rfl

/-- Round trip: the fields come back, the server version padded (or truncated) to 50 bytes. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.format_description_event.FormatDescriptionEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = fdeEnc e) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map fdeView = some { fdeView e with serverVersion := fixedText 50 (cowList e.server_version.1) } ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ ⟨hr, -⟩
  rw [h, fdeRead_fdeEnc] at hr
  simpa [ReadsAs] using hr

/-- `BinlogStruct::len`: the length of what `serialize` writes (`fdeEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (fdeEnc e).length evLenCap ⦄ := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  have hS : binlog.events.format_description_event.FormatDescriptionEvent.SERVER_VER_LEN = 50#usize := by
    unfold binlog.events.format_description_event.FormatDescriptionEvent.SERVER_VER_LEN
      binlog.events.format_description_event.SERVER_VER_LEN; rfl
  have hM : (UScalar.cast .Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hUM : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  simp only [lift, bind_ok, hL, hS]
  step with misc.raw.bytes.RawBytes.len_spec misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple _ rfl as ⟨i, hi⟩
  step*
  have hfl := fixedText_length 50 (cowList e.server_version.1)
  simp_all [sat_add_usize, fdeEnc, fdeLens, evLenCap, misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec]
  have := PKUtil.cowList_length_le e.event_type_header_lengths.1
  omega

/-- `BinlogEvent::EVENT_TYPE`: `FORMAT_DESCRIPTION_EVENT` (15). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .FORMAT_DESCRIPTION_EVENT := by
  unfold binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
