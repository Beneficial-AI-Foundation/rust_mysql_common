import Defs
import Proofs.Util.SharedBasic
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Defs.LemmasG

/-! Helper lemmas shared by several packet proofs (connection, replication, statement and
session-state packets): steps for raw integers and byte strings that several packets read or
write the same way (the pure facts are in `SharedBasic.lean`).

None of them is a global `step` lemma: a file that wants one adds it with
`attribute [local step]`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common.Shared

/-! ## Defaults -/

theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  have e : misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d = ok () := by
    simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  rw [e]; exact (WP.spec_ok _).mpr trivial

theorem rawint_u16_default_spec :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU16.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 core.default.DefaultU16 ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU16.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 core.default.DefaultU16 = ok (0#u16, ()) := by
    simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

theorem rawint_u32_default_spec :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU32.Insts.CoreDefaultDefault
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 core.default.DefaultU32 ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU32.Insts.CoreDefaultDefault
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 core.default.DefaultU32 = ok (0#u32, ()) := by
    simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

/-! ## Little-endian integers -/

theorem parse_unchecked_leu32_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
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

theorem parse_unchecked_leu64_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8)
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

/-- `RawInt<LeU32>::deserialize` on a buffer starting with four given bytes. -/
theorem d_u32 (buf : io.ParseBuf) (x0 x1 x2 x3 : U8) (t : List U8) (hb : buf.val = x0 :: x1 :: x2 :: x3 :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun (o : Option U32) (rest : io.ParseBuf) => o.map (fun v : U32 => v.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry'])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

theorem rawint_u64_ser (x : misc.raw.int.RawInt misc.raw.int.LeU64 U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 x buf
      ⦃ b => b.val = buf.val ++ leBytes 8 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ _ h

/-! ## Byte strings -/

theorem eof_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with PKUtil.eof_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

theorem lenenc_as_str (rb : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  apply WP.spec_bind (PCSUtil.lenenc_as_bytes rb)
  intro s hs
  unfold misc.trusted.from_utf8_lossy
  apply (WP.spec_ok _).mpr
  intro hu
  rw [← hs] at hu
  have hv := (Defs.isUtf8_iff_isValidUTF8 _).1 hu
  exact ⟨s, by simp [hv], hs⟩

theorem u8bytes_as_bytes_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = (cowList rb.1).take 255 ⦄ := by
  have ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm rb)
  intro s hs; rw [hs, hmv]

theorem u8bytes_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid ((cowList rb.1).take 255) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with u8bytes_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

theorem u8bytes_ser (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (u8LenStr ((cowList rb.1).take 255)).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf
      ⦃ b => b.val = buf.val ++ u8LenStr ((cowList rb.1).take 255) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  simp only [u8LenStr, List.length_cons, List.length_take] at h
  apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; omega))
  intro b hb
  rw [hb]
  simp [u8LenStr, Slice.length, hs, Nat.min_comm]

theorem parse_u8bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = checkedLenPrefixed 1 buf.val)
    (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

end mysql_common.Shared
