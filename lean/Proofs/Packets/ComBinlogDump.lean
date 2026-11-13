import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Const.Const
import Proofs.Defs.LemmasG

/-! Statements for `struct ComBinlogDump and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

@[step] private theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  have e : misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d = ok () := by
    simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  rw [e]; exact (WP.spec_ok _).mpr trivial

@[step] private theorem rawint_u32_default_spec :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU32.Insts.CoreDefaultDefault
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 core.default.DefaultU32 ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU32.Insts.CoreDefaultDefault
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 core.default.DefaultU32 = ok (0#u32, ()) := by
    simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

private theorem parse_unchecked_leu32_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4)
    (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

@[step] private theorem const_flags_default_spec :
    misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault = ok (0#u16, ()) := by
    simp [misc.raw._const.Const.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default,
      packets.BinlogDumpFlags.Insts.CoreDefaultDefault.default, packets.BinlogDumpFlags.empty]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] private theorem const_new_flags_spec (flags : packets.BinlogDumpFlags) :
    misc.raw._const.Const.new misc.raw.int.LeU16 flags ⦃ c => c.1 = flags ⦄ := by
  have e : misc.raw._const.Const.new misc.raw.int.LeU16 flags = ok (flags, ()) := rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

private theorem eof_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with eof_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

private theorem const_flags_ser (x : misc.raw._const.Const packets.BinlogDumpFlags misc.raw.int.LeU16)
    (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize packets.BinlogDumpFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U16.Insts.CoreConvertFromBinlogDumpFlags)
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

private theorem flags_try_from_spec (p : U16) :
    packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags.try_from p ⦃ r =>
      (okPart r).map (fun f : packets.BinlogDumpFlags => f.val) =
        if p.val &&& binlogDumpFlagsAll = p.val then some p.val else none ⦄ := by
  unfold packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags.try_from
    packets.BinlogDumpFlags.from_bits packets.BinlogDumpFlags.from_bits_truncate packets.BinlogDumpFlags.all
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hv : i3.val = p.val &&& binlogDumpFlagsAll := by
    have h7 : i2 = 7#u16 := by apply UScalar.eq_of_val_eq; simp_all [UScalar.val_or]
    subst h7; rw [hi3]; simp [UScalar.val_and]; rfl
  split_ifs with h1 h2 h2
  · simp
  · exfalso; apply h2; rw [← hv, h1]
  · exfalso; apply h1; apply UScalar.eq_of_val_eq; rw [hv, h2]
  · simp

private theorem parse_unchecked_flags_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags
      packets.UnknownBinlogDumpFlags.Insts.CoreErrorError) buf () ⦃ r rest =>
      (okPart r).map (fun c => c.1.val) =
        (if leNat (buf.val.take 2) &&& binlogDumpFlagsAll = leNat (buf.val.take 2)
         then some (leNat (buf.val.take 2)) else none) ∧ rest.val = buf.val.drop 2 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
    packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags
    packets.UnknownBinlogDumpFlags.Insts.CoreErrorError buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2)
    (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h)
    (fun p o => o.map (fun c : packets.BinlogDumpFlags => c.val) =
        if p.val &&& binlogDumpFlagsAll = p.val then some p.val else none)
    flags_try_from_spec
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨ho, hrest⟩, hm⟩
  refine ⟨?_, hrest⟩
  cases o with
  | none => simp at ho
  | some p =>
    simp at ho hm
    rw [← ho]
    simpa [Option.map_map, Function.comp_def] using hm

private theorem parse_unchecked_bd_hdr_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple
        18#u8 packets.InvalidComBinlogDumpHeader.Insts.CoreErrorError
        packets.InvalidComBinlogDumpHeader.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = 18) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 18#u8
    packets.InvalidComBinlogDumpHeader.Insts.CoreErrorError
    packets.InvalidComBinlogDumpHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) buf h

private theorem leNat_take_one (l : List U8) (h : 1 ≤ l.length) : leNat (l.take 1) = (l.getD 0 (byte 0)).val := by
  match l, h with
  | a :: _, _ => simp [leNat]

private theorem drop_app_len (l t : List U8) (n : Nat) (h : l.length = n) : (l ++ t).drop n = t := by
  subst h; simp

private theorem binlogDumpRead_enc (d : BinlogDump) (hp : d.pos < 2 ^ 32) (hfl : d.flags < 2 ^ 16)
    (hs : d.serverId < 2 ^ 32) (hf : d.flags &&& binlogDumpFlagsAll = d.flags) :
    binlogDumpRead (binlogDumpEnc d) = (some d, []) := by
  obtain ⟨pos, fl, sid, fn⟩ := d
  dsimp only at *
  have l4 := PBUtil.length_leBytes 4 pos
  have l2 := PBUtil.length_leBytes 2 fl
  have l4s := PBUtil.length_leBytes 4 sid
  unfold binlogDumpRead binlogDumpEnc
  simp only [List.cons_append, List.append_assoc]
  rw [ite_eq_right (by simp only [List.length_cons, List.length_append]; omega)]
  have e1 : (byte 18 :: (leBytes 4 pos ++ (leBytes 2 fl ++ (leBytes 4 sid ++ fn)))).take 11 =
      byte 18 :: (leBytes 4 pos ++ (leBytes 2 fl ++ leBytes 4 sid)) := by
    rw [List.take_succ_cons, ← List.append_assoc, ← List.append_assoc,
      List.take_append_of_le_length (by simp [l4, l2, l4s]), List.take_of_length_le (by simp [l4, l2, l4s]),
      List.append_assoc]
  have e2 : (byte 18 :: (leBytes 4 pos ++ (leBytes 2 fl ++ (leBytes 4 sid ++ fn)))).drop 11 = fn := by
    rw [List.drop_succ_cons, ← List.append_assoc, ← List.append_assoc,
      List.drop_append_of_le_length (by simp [l4, l2, l4s]), List.drop_of_length_le (by simp [l4, l2, l4s]),
      List.nil_append]
  rw [e1, e2]
  simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, byte_val]
  rw [leNat_take_leBytes 4 pos _ (by omega), drop_app_len _ _ 4 l4, leNat_take_leBytes 2 fl _ (by omega),
    show 6 = 4 + 2 from rfl, ← List.drop_drop, drop_app_len _ _ 4 l4, drop_app_len _ _ 2 l2,
    List.take_of_length_le (by omega), PBUtil.leNat_leBytes, Nat.mod_eq_of_lt (by omega)]
  simp [hf]
  omega


/-- `ComBinlogDump::new(server_id)`: position 0, no flags, the server id, an empty file name. -/
theorem packets.ComBinlogDump.new_spec (server_id : U32) :
    packets.ComBinlogDump.new server_id ⦃ d => BinlogDump.of d = ⟨0, 0, server_id.val, []⟩ ⦄ := by
  unfold packets.ComBinlogDump.new
  step*
  simp_all [BinlogDump.of]

/-- `with_pos`: sets the position; nothing else changes. -/
theorem packets.ComBinlogDump.with_pos_spec (self : packets.ComBinlogDump) (pos : U32) :
    packets.ComBinlogDump.with_pos self pos ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with pos := pos.val } ⦄ := by
  unfold packets.ComBinlogDump.with_pos
  step*
  simp_all [BinlogDump.of]

/-- `with_flags`: sets the flags; nothing else changes. -/
theorem packets.ComBinlogDump.with_flags_spec (self : packets.ComBinlogDump) (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDump.with_flags self flags ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with flags := flags.val } ⦄ := by
  unfold packets.ComBinlogDump.with_flags
  step*
  simp_all [BinlogDump.of]

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
theorem packets.ComBinlogDump.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDump) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDump.with_filename into self x ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with filename := cowList c } ⦄ := by
  unfold packets.ComBinlogDump.with_filename
  step*
  simp_all [BinlogDump.of]

/-- `pos`: the field. -/
theorem packets.ComBinlogDump.impl.pos_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.pos self = ok self.pos.1 := by
  rfl

/-- `flags`: the field. -/
theorem packets.ComBinlogDump.impl.flags_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.flags self = ok self.flags.1 := by
  rfl

/-- `server_id`: the field. -/
theorem packets.ComBinlogDump.impl.server_id_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.server_id self = ok self.server_id.1 := by
  rfl

/-- `filename_raw`: the file name. -/
theorem packets.ComBinlogDump.filename_raw_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄ := by
  exact eof_as_bytes_spec _

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComBinlogDump.impl.filename_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.filename self ⦃ c => LossyUtf8Valid (cowList self.filename.1) c ⦄ := by
  exact eof_as_str_spec _

/-- `MySerialize for ComBinlogDump`: appends the protocol's packet `binlogDumpEnc`. -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binlogDumpEnc (BinlogDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ binlogDumpEnc (BinlogDump.of self) ⦄ := by
  unfold packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [binlogDumpEnc, BinlogDump.of, List.length_cons, List.length_append, PBUtil.length_leBytes] at h
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  step with rawint_u32_serialize as ⟨b2, h2⟩
  · simp [alloc.vec.Vec.length, h1] at *; omega
  step with const_flags_ser as ⟨b3, h3⟩
  · simp [alloc.vec.Vec.length, h1, h2] at *; omega
  step with rawint_u32_serialize as ⟨b4, h4⟩
  · simp [alloc.vec.Vec.length, h1, h2, h3] at *; omega
  apply WP.spec_mono (eof_ser _ _ (by simp [alloc.vec.Vec.length, h1, h2, h3, h4] at *; omega))
  intro b hb
  rw [hb, h4, h3, h2, h1]
  simp [binlogDumpEnc, BinlogDump.of]
  rfl

/-- `MyDeserialize for ComBinlogDump`: `SIZE` is `None`. -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ComBinlogDump`: total; `binlogDumpRead` (11 bytes, then the file name is
    the rest of the input). -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map BinlogDump.of, rest.val) = binlogDumpRead buf.val ⦄ := by
  unfold packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize binlogDumpRead
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 11 := hl
    rw [ite_eq_right (by omega)]
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rest, hbuf⟩ :
        ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 rest, (↑buf : List U8) =
          a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: rest, _ =>
        exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
    simp at h1a h1b
    simp only [CoreOpsTry.branch, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
      List.take_zero, List.getD_cons_zero]
    step with parse_unchecked_bd_hdr_spec as ⟨r1, sbuf, h2a, h2b⟩
    rw [h1a] at h2a h2b
    simp [leNat] at h2a h2b
    cases r1 with
    | Err e =>
      have ha : a0.val ≠ 0x12 := by intro h; simp [h] at h2a
      rw [ite_eq_left (Or.inl ha), ← h1b]
      simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok hd =>
    have ha : a0.val = 0x12 := by simpa using h2a
    simp only
    step with parse_unchecked_leu32_spec as ⟨r2, sbuf2, h3a, h3b⟩
    · simp [Slice.length, h2b]
    cases r2 with
    | Err e => simp at h3a
    | Ok posv =>
    simp only [okPart_Ok, Option.map_some, Option.some.injEq, h2b] at h3a h3b
    simp only
    step with parse_unchecked_flags_spec as ⟨r3, sbuf3, h4a, h4b⟩
    · simp [Slice.length, h3b]
    simp only [h3b, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero] at h4a h4b
    cases r3 with
    | Err e =>
      simp only [okPart_Err, Option.map_none] at h4a
      have hf : leNat [a5, a6] &&& binlogDumpFlagsAll ≠ leNat [a5, a6] := by
        intro h; simp [h] at h4a
      rw [ite_eq_left (Or.inr hf), ← h1b]
      simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok flv =>
    have hf : leNat [a5, a6] &&& binlogDumpFlagsAll = leNat [a5, a6] := by
      by_contra h; simp [h] at h4a
    simp only [hf, ↓reduceIte] at h4a
    rw [ite_eq_right (by simp [ha, hf])]
    simp only
    step with parse_unchecked_leu32_spec as ⟨r4, sbuf4, h5a, h5b⟩
    · simp [Slice.length, h4b]
    cases r4 with
    | Err e => simp at h5a
    | Ok sidv =>
    simp only
    step with parse_eof_bytes_spec as ⟨r5, buf2, h6a, h6b⟩
    cases r5 with
    | Err e => simp at h6a
    | Ok rb =>
    simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h4a h5a h6a
    simp only [h4b, List.take_succ_cons, List.take_zero] at h5a
    simp [BinlogDump.of, h3a, h4a, h5a, h6a, h6b, h1b]
  · obtain ⟨h1a, h1b⟩ := h1
    subst h1b
    rw [ite_eq_left (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- Round trip: a packet with known flags, in the protocol layout, is read back (the file name
    takes the rest of the input). -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (d : packets.ComBinlogDump)
    (hf : (BinlogDump.of d).flags &&& binlogDumpFlagsAll = (BinlogDump.of d).flags)
    (buf : io.ParseBuf) (h : buf.val = binlogDumpEnc (BinlogDump.of d)) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map BinlogDump.of = some (BinlogDump.of d) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  rw [h, binlogDumpRead_enc _ (by simp [BinlogDump.of]; scalar_tac) (by simp [BinlogDump.of]; scalar_tac)
    (by simp [BinlogDump.of]; scalar_tac) hf] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
