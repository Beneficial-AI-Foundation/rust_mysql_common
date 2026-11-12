import Defs
import Proofs.Util.PacketsOkErr

/-! Statements for `struct ProgressReport and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

/-- `new`: the given fields (the stage info converted with `into`). -/
theorem packets.ProgressReport.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (stage max_stage : U8) (progress : U32) (stage_info : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into stage_info = ok c) :
    packets.ProgressReport.new into stage max_stage progress stage_info ⦃ p =>
      p.stage.1 = stage ∧ p.max_stage.1 = max_stage ∧ p.progress.1 = progress ∧ p.stage_info.1 = c ⦄ := by
  unfold packets.ProgressReport.new
  step*

/-- `stage`: the field. -/
theorem packets.ProgressReport.impl.stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.stage self = ok self.stage.1 := by
  rfl

/-- `max_stage`: the field. -/
theorem packets.ProgressReport.impl.max_stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.max_stage self = ok self.max_stage.1 := by
  rfl

/-- `progress`: the field. -/
theorem packets.ProgressReport.impl.progress_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.progress self = ok self.progress.1 := by
  rfl

/-- `stage_info_ref`: the stage info bytes. -/
theorem packets.ProgressReport.stage_info_ref_spec (self : packets.ProgressReport) :
    packets.ProgressReport.stage_info_ref self ⦃ s => s.val = cowList self.stage_info.1 ⦄ := by
  unfold packets.ProgressReport.stage_info_ref
  exact lenenc_as_bytes_spec _

/-- `into_owned`: the same fields. -/
theorem packets.ProgressReport.into_owned_spec (self : packets.ProgressReport) :
    packets.ProgressReport.into_owned self ⦃ p => Progress.of p = Progress.of self ⦄ := by
  unfold packets.ProgressReport.into_owned
  step*
  simp_all [Progress.of]

/-- `MyDeserialize for ProgressReport`: `SIZE` is `None`. -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ProgressReport`: total; `progressRead`. -/
@[step]
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Progress.of, rest.val) = progressRead buf.val ⦄ := by
  unfold packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize progressRead
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 6 := hl
    rw [if_neg (by omega)]
    obtain ⟨a0, a1, a2, a3, a4, a5, rest, hbuf⟩ :
        ∃ a0 a1 a2 a3 a4 a5 rest, (↑buf : List U8) = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest, _ => exact ⟨a0, a1, a2, a3, a4, a5, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
      simp at h1a h1b
      simp only [CoreOpsTry.branch, bind_tc_ok]
      step as ⟨sbuf, hs⟩
      step with parse_unchecked_u8_spec as ⟨r1, sbuf1, h2a, h2b⟩
      · simp [Slice.length, hs, h1a]
      cases r1 with
      | Err e => simp at h2a
      | Ok st =>
      simp only [CoreOpsTry.branch, bind_tc_ok]
      step with parse_unchecked_u8_spec as ⟨r2, sbuf2, h3a, h3b⟩
      · simp [Slice.length, h2b, hs, h1a]
      cases r2 with
      | Err e => simp at h3a
      | Ok mst =>
      simp only [CoreOpsTry.branch, bind_tc_ok]
      step with parse_unchecked_leu24_spec as ⟨r3, sbuf3, h4a, h4b⟩
      · simp [Slice.length, h3b, h2b, hs, h1a]
      cases r3 with
      | Err e => simp at h4a
      | Ok pr =>
      simp only [CoreOpsTry.branch, bind_tc_ok]
      step with parse_lenenc_bytes_spec h64 as ⟨r4, buf2, h5⟩
      rw [h1b] at h5
      simp only [List.drop_succ_cons, List.drop_zero]
      rw [← h5]
      cases r4 with
      | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok rb =>
        simp [h1a, hs, h2b, h3b, leNat] at h2a h3a h4a
        simp [CoreOpsTry.branch, Progress.of, h2a, h3a, h4a, leNat]
  · obtain ⟨h1a, rfl⟩ := h1
    rw [if_pos (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- `MySerialize for ProgressReport`: appends `progressEnc` (the progress truncated to 3 bytes). -/
@[step]
theorem packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ProgressReport) (buf : alloc.vec.Vec U8)
    (h : buf.length + (progressEnc (Progress.of self)).length ≤ Usize.max) :
    packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ progressEnc (Progress.of self) ⦄ := by
  unfold packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [progressEnc, Progress.of, List.length_cons, List.length_append, length_leBytes, vec_len] at h
  step with put_u8_spec as ⟨b1, h1⟩
  step with rawint_u8_ser as ⟨b2, h2⟩
  · simp [vec_len, h1]; omega
  step with rawint_u8_ser as ⟨b3, h3⟩
  · simp [vec_len, h2, h1]; omega
  step with rawint_leu24_ser as ⟨b4, h4⟩
  · simp [vec_len, h3, h2, h1]; omega
  apply WP.spec_mono (lenenc_ser _ _ (by simp [vec_len, h4, h3, h2, h1, length_leBytes]; omega))
  intro b hb
  rw [hb, h4, h3, h2, h1]
  simp [progressEnc, Progress.of, byte_val_self]
  rfl

/-- Round trip: `deserialize` reads back what `serialize` writes, when the progress fits in 3 bytes. -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (p : packets.ProgressReport) (hp : p.progress.1.val < 2 ^ 24) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = progressEnc (Progress.of p) ++ tail) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Progress.of = some (Progress.of p) ∧ rest.val = tail ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  simp only [progressEnc, List.length_append, List.length_cons, lenencStr] at hlen
  apply WP.spec_mono (packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
  rintro ⟨r, rest⟩ hr
  rw [h, progressRead_enc _ _ (by simp [Progress.of]; scalar_tac) (by simp [Progress.of]; scalar_tac) hp
    (by simp [Progress.of] at hlen ⊢; omega)] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
