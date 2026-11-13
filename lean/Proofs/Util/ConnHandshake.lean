import Defs
import Proofs.Defs.LemmasConn
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Const.RawConst
import Proofs.Misc.Raw.Skip
import Proofs.Misc.Raw.Array
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU32LowerHalf
import Proofs.Misc.Raw.Int.LeU32UpperHalf
import Proofs.Misc.Raw.Bytes.NullBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Misc.Raw.Bytes.U8Bytes

/-! Helper lemmas for the handshake packet proofs (`Proofs/Packets/{HandshakePacket,
HandshakeResponse,SslRequest}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil

namespace mysql_common.ConnHSUtil

/-! ## Fixed-width readers through `parse_unchecked` -/

theorem pu_rawint_leu32 (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
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

theorem pu_rawconst {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (k : Nat) (g : P → Nat)
    (buf : io.ParseBuf) (F : List U8 → Nat)
    (h : inst.deserialize buf ⦃ r rest => (okPart r).map g = some (F (buf.val.take k)) ∧ rest.val = buf.val.drop k ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U inst) buf ()
      ⦃ r rest => (okPart r).map (fun x => g x.1) = some (F (buf.val.take k)) ∧ rest.val = buf.val.drop k ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec U inst buf
    (fun o rest => o.map g = some (F (buf.val.take k)) ∧ rest.val = buf.val.drop k) h
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

theorem pu_rawconst_leu32 (U : Type) (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf ()
      ⦃ r rest => (okPart r).map (fun x => x.1.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  have h1 := misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h
  exact pu_rawconst U misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 4 (·.val) buf leNat h1

theorem pu_rawconst_lower (U : Type) (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf ()
      ⦃ r rest => (okPart r).map (fun x => x.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  have h1 := misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h
  exact pu_rawconst U misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32 2 (·.val) buf leNat h1

theorem pu_rawconst_upper (U : Type) (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf ()
      ⦃ r rest => (okPart r).map (fun x => x.1.val) = some (leNat (buf.val.take 2) * 2 ^ 16) ∧ rest.val = buf.val.drop 2 ⦄ := by
  have h1 := misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h
  exact pu_rawconst U misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32 2 (·.val) buf (fun l => leNat l * 2 ^ 16) h1

theorem pu_skip (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple LEN) buf ()
      ⦃ r rest => (okPart r).isSome ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec LEN buf h

theorem pu_array (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    io.ParseBuf.parse_unchecked (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple LEN) buf ()
      ⦃ r rest => (okPart r).map (·.val) = some (buf.val.take LEN.val) ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec LEN buf h

/-! ## Flags -/

@[step]
theorem mariadb_from_bits_truncate_spec (bits : U32) :
    constants.MariadbCapabilities.from_bits_truncate bits ⦃ r => r.val = bits.val &&& mariadbCapabilitiesAll ⦄ := by
  simp only [constants.MariadbCapabilities.from_bits_truncate, constants.MariadbCapabilities.all, lift, bind_ok]
  simp [mariadbCapabilitiesAll]

theorem and_all32 (x : Nat) (h : x < 2 ^ 32) : x &&& capabilityFlagsAll = x := by
  rw [capabilityFlagsAll, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem leNat_take_lt (l : List U8) (k : Nat) : leNat (l.take k) < 2 ^ (8 * k) := by
  have := leNat_lt (l.take k)
  have h2 : 2 ^ (8 * (l.take k).length) ≤ 2 ^ (8 * k) := Nat.pow_le_pow_right (by norm_num) (by simp)
  omega

/-! ## Serializers -/

@[step]
theorem const_caps_u32_ser (x : misc.raw._const.Const constants.CapabilityFlags misc.raw.int.LeU32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.CapabilityFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U32.Insts.CoreConvertFromCapabilityFlags)
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ b => b.val = buf.val ++ leBytes 4 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

@[step]
theorem const_mariadb_u32_ser (x : misc.raw._const.Const constants.MariadbCapabilities misc.raw.int.LeU32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.MariadbCapabilities.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U32.Insts.CoreConvertFromMariadbCapabilities)
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ b => b.val = buf.val ++ leBytes 4 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

@[step]
theorem const_caps_lower_ser (x : misc.raw._const.Const constants.CapabilityFlags misc.raw.int.LeU32LowerHalf) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.CapabilityFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U32.Insts.CoreConvertFromCapabilityFlags)
      misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

@[step]
theorem const_caps_upper_ser (x : misc.raw._const.Const constants.CapabilityFlags misc.raw.int.LeU32UpperHalf) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.CapabilityFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U32.Insts.CoreConvertFromCapabilityFlags)
      misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 (x.1.val / 2 ^ 16) ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

/-! ## Wire layouts -/

theorem leNat_bytes4 (n : Nat) :
    leNat [byte n, byte (n / 256), byte (n / 256 / 256), byte (n / 256 / 256 / 256)] = n % 2 ^ 32 := by
  simp [leNat, byte_val]; omega

theorem leNat_bytes2 (n : Nat) : leNat [byte n, byte (n / 256)] = n % 2 ^ 16 := by
  simp [leNat, byte_val]; omega

theorem leNat_bytes1 (n : Nat) : leNat [byte n] = n % 256 := by
  simp [leNat, byte_val]

theorem sslRequestRead_enc (v : SslReq) (hv : v.caps < 2 ^ 32 ∧ v.maxPacket < 2 ^ 32 ∧ v.charset < 256 ∧
      v.mariadbCaps &&& mariadbCapabilitiesAll = v.mariadbCaps) (tail : List U8) :
    sslRequestRead (sslRequestEnc v ++ tail) = (some v, tail) := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hP : ¬ ((sslRequestEnc v ++ tail).length < 32) := by
    simp [sslRequestEnc, PBUtil.length_leBytes]; omega
  unfold sslRequestRead
  simp only [hP, ↓reduceIte]
  unfold sslRequestEnc
  simp only [leBytes, List.replicate, List.cons_append, List.nil_append]
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  rw [leNat_bytes4, leNat_bytes4, leNat_bytes4, leNat_bytes1, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]
  have h5 : v.mariadbCaps < 2 ^ 32 := by
    have : v.mariadbCaps &&& mariadbCapabilitiesAll ≤ mariadbCapabilitiesAll := Nat.and_le_right
    rw [h4] at this; simp [mariadbCapabilitiesAll] at this; omega
  rw [Nat.mod_eq_of_lt h5, h4]

end mysql_common.ConnHSUtil
