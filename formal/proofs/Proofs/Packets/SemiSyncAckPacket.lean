import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Defs.LemmasG
import Proofs.Util.Shared

/-! Statements for `struct SemiSyncAckPacket and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.Shared
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

attribute [local step] constu8_default_spec

private theorem parse_unchecked_ss_hdr_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple
        239#u8 packets.InvalidSemiSyncAckPacketPacketHeader.Insts.CoreErrorError
        packets.InvalidSemiSyncAckPacketPacketHeader.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = 239) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 239#u8
    packets.InvalidSemiSyncAckPacketPacketHeader.Insts.CoreErrorError
    packets.InvalidSemiSyncAckPacketPacketHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) buf h


/-- `SemiSyncAckPacket::new(position, filename)`: the position and the file name
    (`filename.into()`). -/
theorem packets.SemiSyncAckPacket.new_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (position : U64) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.new into position filename ⦃ p =>
      p.position.1 = position ∧ p.filename.1 = c ⦄ := by
  unfold packets.SemiSyncAckPacket.new
  step*

/-- `with_position`: sets the position; nothing else changes. -/
theorem packets.SemiSyncAckPacket.with_position_spec (self : packets.SemiSyncAckPacket) (position : U64) :
    packets.SemiSyncAckPacket.with_position self position ⦃ p =>
      p.position.1 = position ∧ p.filename = self.filename ⦄ := by
  unfold packets.SemiSyncAckPacket.with_position
  obtain ⟨hd, ⟨x, pd⟩, f⟩ := self
  exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩

/-- `with_filename`: sets the file name; nothing else changes. -/
theorem packets.SemiSyncAckPacket.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.SemiSyncAckPacket) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.with_filename into self filename ⦃ p =>
      p.position = self.position ∧ p.filename.1 = c ⦄ := by
  unfold packets.SemiSyncAckPacket.with_filename
  step*

/-- `position`: the field. -/
theorem packets.SemiSyncAckPacket.impl.position_eq (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.position self = ok self.position.1 := by
  rfl

/-- `filename_raw`: the file name. -/
theorem packets.SemiSyncAckPacket.filename_raw_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄ := by
  exact eof_as_bytes_spec _

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.SemiSyncAckPacket.impl.filename_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.filename self ⦃ c => LossyUtf8Valid (cowList self.filename.1) c ⦄ := by
  exact eof_as_str_spec _

/-- `MySerialize for SemiSyncAckPacket`: appends `semiSyncAckEnc` (`0xEF`, the position, the
    file name). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SemiSyncAckPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 9 + (cowList self.filename.1).length ≤ Usize.max) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ semiSyncAckEnc self.position.1.val (cowList self.filename.1) ⦄ := by
  unfold packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  step with rawint_u64_ser as ⟨b2, h2⟩
  · simp [alloc.vec.Vec.length, h1] at *; omega
  apply WP.spec_mono (eof_ser _ _ (by simp [alloc.vec.Vec.length, h1, h2] at *; omega))
  intro b hb
  rw [hb, h2, h1]
  simp [semiSyncAckEnc]
  rfl

/-- `MyDeserialize for SemiSyncAckPacket`: `SIZE` is `None`. -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for SemiSyncAckPacket`: total; `semiSyncAckRead` (9 bytes, then the file name
    is the rest of the input). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (p.position.1.val, cowList p.filename.1)), rest.val) =
        semiSyncAckRead buf.val ⦄ := by
  unfold packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize semiSyncAckRead
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 9 := hl
    rw [ite_eq_right (by omega)]
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rest, hbuf⟩ :
        ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 rest, (↑buf : List U8) =
          a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest, _ =>
        exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
    simp at h1a h1b
    simp only [CoreOpsTry.branch, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
      List.take_zero, List.getD_cons_zero]
    step with parse_unchecked_ss_hdr_spec as ⟨r1, sbuf, h2a, h2b⟩
    rw [h1a] at h2a h2b
    simp [leNat] at h2a h2b
    cases r1 with
    | Err e =>
      have ha : a0.val ≠ 0xEF := by intro h; simp [h] at h2a
      rw [ite_eq_left ha, ← h1b]
      simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok hd =>
    have ha : a0.val = 0xEF := by simpa using h2a
    rw [ite_eq_right (by simp [ha])]
    simp only
    step with parse_unchecked_leu64_spec as ⟨r2, sbuf2, h3a, h3b⟩
    · simp [Slice.length, h2b]
    cases r2 with
    | Err e => simp at h3a
    | Ok posv =>
    simp only
    step with parse_eof_bytes_spec as ⟨r3, buf2, h4a, h4b⟩
    cases r3 with
    | Err e => simp at h4a
    | Ok rb =>
    simp only [okPart_Ok, Option.map_some, Option.some.injEq, h2b] at h3a h4a
    simp [h3a, h4a, h4b, h1b]
  · obtain ⟨h1a, h1b⟩ := h1
    subst h1b
    rw [ite_eq_left (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- Round trip: `semiSyncAckEnc` is read back (the file name takes the rest of the input). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.SemiSyncAckPacket) (buf : io.ParseBuf)
    (h : buf.val = semiSyncAckEnc p.position.1.val (cowList p.filename.1)) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun q => (q.position.1.val, cowList q.filename.1)) =
        some (p.position.1.val, cowList p.filename.1) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  have hp : p.position.1.val < 2 ^ 64 := by scalar_tac
  have e : semiSyncAckRead buf.val = (some (p.position.1.val, cowList p.filename.1), []) := by
    rw [h]
    unfold semiSyncAckEnc semiSyncAckRead
    have l8 := PBUtil.length_leBytes 8 p.position.1.val
    simp only [List.cons_append, List.length_cons, List.length_append, l8, List.getD_cons_zero, byte_val,
      List.drop_succ_cons, List.drop_zero]
    rw [ite_eq_right (by omega), ite_eq_right (by norm_num), leNat_take_leBytes 8 _ _ hp,
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  rw [e] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
