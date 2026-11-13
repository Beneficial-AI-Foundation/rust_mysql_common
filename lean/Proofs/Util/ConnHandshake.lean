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
import Proofs.Defs.LemmasG
import Proofs.Util.ConvBytesTime
import Proofs.Constants.CapabilityFlags
import Proofs.Util.ConnAuth
import Proofs.Misc.Raw.Int.U8
import Proofs.Packets.AuthPlugin
import Proofs.Util.Shared

/-! Helper lemmas for the handshake packet proofs (`Proofs/Packets/{HandshakePacket,
HandshakeResponse,SslRequest}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.Shared
open core.result.Result.Insts

namespace mysql_common.ConnHSUtil

/-! ## Fixed-width readers through `parse_unchecked` -/

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

/-! ## `RawBytes` accessors -/

@[step]
theorem nullbytes_as_bytes (rb : misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = cowList rb.1 ⦄ := by
  have hm : misc.raw.bytes.BytesRepr.MAX_LEN misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple =
      ok misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN := rfl
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ _ hm rb)
  intro s hs
  rw [hs, misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec]
  exact List.take_of_length_le (PCSUtil.cowList_length_le _)

@[step]
theorem barebytes_as_bytes (rb : misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 247#usize) Usize) :
    misc.raw.bytes.RawBytes.as_bytes (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize) rb
      ⦃ s => s.val = (cowList rb.1).take 247 ⦄ := by
  have hm : (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize).MAX_LEN = ok 247#usize := by
    simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ _ hm rb)
  intro s hs
  rw [hs]; rfl

theorem from_utf8_lossy_spec (s : Slice U8) :
    misc.trusted.from_utf8_lossy s ⦃ c => LossyUtf8 s.val c ⦄ := by
  unfold misc.trusted.from_utf8_lossy
  apply (WP.spec_ok _).mpr
  by_cases h : IsUtf8 s.val
  · have h' := (Defs.isUtf8_iff_isValidUTF8 _).1 h
    simp only [h', ite_true]
    exact ⟨fun _ => ⟨s, rfl, rfl⟩, fun hn => absurd h hn⟩
  · have h' : ¬ (Trusted.bytesOf s.val).IsValidUTF8 := fun h' => h ((Defs.isUtf8_iff_isValidUTF8 _).2 h')
    simp only [h', ite_false]
    exact ⟨fun hy => absurd hy h, fun _ => ⟨_, rfl⟩⟩

@[step]
theorem nullbytes_as_str (rb : misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8 (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  apply WP.spec_bind (nullbytes_as_bytes rb)
  intro s hs
  rw [← hs]
  exact from_utf8_lossy_spec s

/-! ## Server versions -/

/-- A version group: 1–3 ASCII digits. -/
def GoodGroup (l : List U8) : Prop := l ≠ [] ∧ l.all isDigit = true ∧ l.length ≤ 3

theorem btoi_u16_good (s : Slice U8) (h : GoodGroup s.val) :
    ∃ x, Trusted.btoiUnsigned .U16 s = some x ∧ x.val = digitsVal s.val := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : digitsVal s.val < 2 ^ UScalarTy.U16.numBits := by
    have := CBTUtil.digitsVal_lt s.val h2
    have : 10 ^ s.val.length ≤ 10 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    simp [UScalarTy.numBits]; omega
  have hv : Trusted.btoiValue? s.val = some (digitsVal s.val : Int) := by
    obtain ⟨b, rest, hbr⟩ : ∃ b rest, s.val = b :: rest := by
      cases hs : s.val with
      | nil => exact absurd hs h1
      | cons b rest => exact ⟨b, rest, rfl⟩
    have hd : isDigit b = true := by rw [hbr] at h2; simp at h2; exact h2.1
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    rw [hbr]
    simp only [Trusted.btoiValue?, show ¬ b.val = 43 by omega, show ¬ b.val = 45 by omega, ite_false]
    rw [← hbr, CBTUtil.decimalDigits_eq _ h1 h2]
    rfl
  simp only [Trusted.btoiUnsigned, hv, Option.bind_some]
  simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast]
  have := UScalar.tryMkOpt_eq .U16 (digitsVal s.val)
  cases hc : UScalar.tryMkOpt .U16 (digitsVal s.val) with
  | none => rw [hc] at this; exfalso; apply this; simpa [UScalar.inBounds] using hb
  | some x => rw [hc] at this; exact ⟨x, rfl, this.1⟩

theorem versionOfCaptures_good (C : Option (Slice U8 × Slice U8 × Slice U8))
    (hC : ∀ a b c, C = some (a, b, c) → GoodGroup a.val ∧ GoodGroup b.val ∧ GoodGroup c.val) :
    versionOfCaptures C ⦃ r => versionVal r = digitsTriple (capturesVal C) ⦄ := by
  rcases C with _ | ⟨a, b, c⟩
  · simp [versionOfCaptures, versionVal, digitsTriple, capturesVal, Trusted.capturesVal]
  · obtain ⟨ga, gb, gc⟩ := hC a b c rfl
    obtain ⟨x, hx, hxv⟩ := btoi_u16_good a ga
    obtain ⟨y, hy, hyv⟩ := btoi_u16_good b gb
    obtain ⟨z, hz, hzv⟩ := btoi_u16_good c gc
    simp [versionOfCaptures, hx, hy, hz, versionVal, digitsTriple, capturesVal, Trusted.capturesVal, hxv, hyv, hzv]

theorem reDigitRun_all (l : List U8) : (Trusted.reDigitRun l).all isDigit = true := by
  unfold Trusted.reDigitRun
  rw [← CBTUtil.isAsciiDigit_eq]
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.takeWhile_cons]
    split <;> simp_all

theorem reTwoGroups_good (bs : List U8) (g1 g2 r : List U8) (h : Trusted.reTwoGroups bs = some (g1, g2, r)) :
    GoodGroup g1 ∧ GoodGroup g2 := by
  unfold Trusted.reTwoGroups at h
  simp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, -⟩ := h
  refine ⟨⟨?_, reDigitRun_all _, by omega⟩, ⟨?_, reDigitRun_all _, by omega⟩⟩
  · intro hn; rw [hn] at h1; simp at h1
  · intro hn; rw [hn] at h2; simp at h2

theorem versionReMatch_good (bs : List U8) (g1 g2 g3 : List U8) (h : versionReMatch bs = some (g1, g2, g3)) :
    GoodGroup g1 ∧ GoodGroup g2 ∧ GoodGroup g3 := by
  unfold versionReMatch Trusted.versionReMatch at h
  split at h
  · rename_i a b r hr
    obtain ⟨ga, gb⟩ := reTwoGroups_good _ _ _ _ hr
    simp only at h
    split_ifs at h with h3
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨ga, gb, ?_, ?_, by simp⟩
    · intro hn
      have := congrArg List.length hn
      simp only [List.length_take, List.length_nil] at this
      omega
    · have := reDigitRun_all r
      rw [List.all_eq_true] at this ⊢
      intro x hx; exact this x (List.mem_of_mem_take hx)
  · simp at h

theorem reMariadbCore_good (bs : List U8) (g1 g2 g3 : List U8) (h : Trusted.reMariadbCore bs = some (g1, g2, g3)) :
    GoodGroup g1 ∧ GoodGroup g2 ∧ GoodGroup g3 := by
  unfold Trusted.reMariadbCore at h
  split at h
  · rename_i a b r hr
    obtain ⟨ga, gb⟩ := reTwoGroups_good _ _ _ _ hr
    rcases ht : Trusted.reMariadbTail r with _ | t
    · simp [ht] at h
    · simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨ga, gb, ?_⟩
      unfold Trusted.reMariadbTail at ht
      simp only at ht
      split_ifs at ht with hc
      simp only [Option.some.injEq] at ht
      subst ht
      refine ⟨?_, reDigitRun_all _, hc.2.1⟩
      intro hn; have := hc.1; rw [hn] at this; simp at this
  · simp at h

theorem mariadbVersionReMatch_good (bs : List U8) (g1 g2 g3 : List U8) (h : mariadbVersionReMatch bs = some (g1, g2, g3)) :
    GoodGroup g1 ∧ GoodGroup g2 ∧ GoodGroup g3 := by
  unfold mariadbVersionReMatch Trusted.mariadbVersionReMatch at h
  simp only at h
  split at h
  · rename_i g hg
    rw [h] at hg
    split_ifs at hg
    · exact reMariadbCore_good _ _ _ _ hg
  · exact reMariadbCore_good _ _ _ _ h

/-! ## Trailing `0` -/

theorem dropTrailingNul_nil : dropTrailingNul [] = [] := rfl

theorem dropTrailingNul_length_le (l : List U8) : (dropTrailingNul l).length ≤ l.length := by
  unfold dropTrailingNul
  split
  · split <;> simp
  · simp

theorem dropTrailingNul_last_zero (l : List U8) (h : 0 < l.length) (h0 : l[l.length - 1]! = 0#u8) :
    dropTrailingNul l = l.take (l.length - 1) := by
  unfold dropTrailingNul
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
  simp only [h0]
  simp [List.dropLast_eq_take]

theorem dropTrailingNul_last_ne (l : List U8) (h : 0 < l.length) (h0 : ¬ l[l.length - 1]! = 0#u8) :
    dropTrailingNul l = l := by
  unfold dropTrailingNul
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
  have : ¬ (l[l.length - 1]).val = 0 := fun hh => h0 (UScalar.eq_of_val_eq (by simpa using hh))
  simp only [this, ite_false]

@[step]
theorem extend_from_slice_u8 (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ v' => v'.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intro x _; rfl))
  intro l hl
  simp [hl.1]

@[step]
theorem const_status_ser (x : misc.raw._const.Const constants.StatusFlags misc.raw.int.LeU16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.StatusFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U16.Insts.CoreConvertFromStatusFlags)
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

@[step]
theorem nullbytes_raw_ser (rb : misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (nulStr (cowList rb.1)).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf
      ⦃ b => b.val = buf.val ++ nulStr (cowList rb.1) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by rw [hs]; simp [nulStr] at h; simp; omega))
  intro b hb; rw [hb, hs]; simp [nulStr]

@[step]
theorem barebytes_raw_ser (rb : misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 247#usize) Usize) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((cowList rb.1).take 247).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize) rb buf
      ⦃ b => b.val = buf.val ++ (cowList rb.1).take 247 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec _ s buf
    (by simp only [Slice.length, hs]; simp at h; simp; omega))
  intro b hb; rw [hb, hs]; rfl

theorem barebytes_len (rb : misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 247#usize) Usize) :
    misc.raw.bytes.RawBytes.len (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize) rb
      ⦃ n => n.val = min (cowList rb.1).length 247 ⦄ := by
  have hm : (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize).MAX_LEN = ok 247#usize := by
    simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]
  exact misc.raw.bytes.RawBytes.len_spec _ _ hm rb

@[step]
theorem handshake_auth_plugin_data_len_spec (b : Bool)
    (s2 : Option (misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 247#usize) Usize)) :
    packets.handshake_auth_plugin_data_len b s2 ⦃ i =>
      i.val = if b then (match s2 with | some rb => min (cowList rb.1).length 247 + 8 | none => 0) else 0 ⦄ := by
  unfold packets.handshake_auth_plugin_data_len
  cases b
  · simp
  · rcases s2 with _ | rb
    · simp
    · simp only [ite_true]
      step with barebytes_len as ⟨n, hn⟩
      step*

@[step]
theorem caps_bits_spec (x : constants.CapabilityFlags) :
    constants.CapabilityFlags.bits x ⦃ r => r = x ⦄ := by
  simp [constants.CapabilityFlags.bits]

theorem and_pow_pos_iff (x : Nat) (k : Nat) : (x &&& 2 ^ k > 0) ↔ hasFlag x (2 ^ k) = true := by
  rw [PCSUtil.and_two_pow, ConnHS.hasFlag_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x / 2 ^ k % 2 = 1 <;> simp [h]

theorem u32_and_pos_iff (x c : U32) (k : Nat) (hc : c.val = 2 ^ k) :
    (x &&& c > 0#u32) ↔ hasFlag x.val (2 ^ k) = true := by
  rw [← and_pow_pos_iff, ← hc]
  have : (x &&& c).val = x.val &&& c.val := by simp
  constructor
  · intro h; have : (0#u32).val < (x &&& c).val := h; simp_all
  · intro h; show (0#u32).val < (x &&& c).val; simp_all

theorem leNat_take1_drop (l : List U8) (i : Nat) (h : i < l.length) :
    leNat ((l.drop i).take 1) = (l.getD i (byte 0)).val := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    cases i with
    | zero => simp [leNat]
    | succ i => simp only [List.drop_succ_cons, List.getD_cons_succ]; exact ih i (by simp at h; omega)

theorem field_take31 (l : List U8) (i k : Nat) (h : i + k ≤ 31) :
    ((l.take 31).drop i).take k = (l.drop i).take k := by
  rw [List.drop_take, List.take_take]; congr 1; omega

theorem hcast_i8_val (x : U8) :
    ((UScalar.hcast .I8 x).val : Int) = if x.val < 128 then (x.val : Int) else (x.val : Int) - 256 := by
  rw [UScalar.hcast_val_eq]
  have hx : x.val < 256 := by scalar_tac
  simp only [IScalarTy.numBits, Int.bmod]
  split_ifs <;> omega

@[step]
theorem max_i8_spec (x y : I8) :
    core.cmp.max core.cmp.OrdI8 x y ⦃ r => r.val = max x.val y.val ⦄ := by
  simp [core.cmp.max]

theorem parse_barebytes_spec (buf : io.ParseBuf) (len : Usize) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize)) buf len ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (fun rb => cowList rb.1) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq])]
  have H := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
    (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 247#usize) len buf
    (fun o rest => if len.val ≤ buf.length then o = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else o = none ∧ rest = buf) (by
    apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec 247#usize len buf)
    rintro ⟨r, rest⟩ hr
    simp only [WP.uncurry'_pair] at hr ⊢
    split_ifs at hr ⊢ with hc
    · exact hr
    · rw [hr.1]; exact ⟨rfl, hr.2⟩)
  apply WP.spec_mono H
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'_pair] at hr ⊢
  split_ifs at hr ⊢
  · exact hr
  · exact ⟨by simpa using hr.1, hr.2⟩

theorem scramble_len_val (lb : U8) (i4 i5 i6 : I8) (len : Usize) (h4 : i4 = UScalar.hcast .I8 lb)
    (h5 : i5.val = i4.val - 8) (h6 : i6.val = max 13 i5.val) (hl : len = IScalar.hcast .Usize i6) : len.val = scramble2LenCrate lb.val := by
  have hb : lb.val < 256 := by scalar_tac
  have h4' := hcast_i8_val lb
  rw [← h4] at h4'
  have hi6 : 13 ≤ i6.val ∧ i6.val ≤ 127 := by
    rw [h6, h5, h4']; split_ifs <;> omega
  have hp : (2 : Int) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    have := IntAndMisc.usize_pow_ge; exact_mod_cast this
  rw [hl, IScalar.hcast_val_eq, Int.emod_eq_of_lt (by omega) (by omega), scramble2LenCrate]
  rw [h6, h5, h4']
  split_ifs <;> omega

theorem setflag_spec (x bit : constants.CapabilityFlags) (c : Prop) (d : Decidable c) :
    (@ite _ c d (constants.CapabilityFlags.insert x bit) (constants.CapabilityFlags.remove x bit))
      ⦃ r => r.val = setFlag x.val bit.val (@decide c d) ⦄ := by
  by_cases hc : c
  · simp only [hc, ite_true]
    apply WP.spec_mono (constants.CapabilityFlags.insert_spec x bit)
    intro r hr; simp [hr, setFlag]
  · simp only [hc, ite_false]
    apply WP.spec_mono (constants.CapabilityFlags.remove_spec x bit)
    intro r hr; simp [hr, setFlag]

@[step]
theorem rawbytes_new_borrowed (s : Slice U8) :
    misc.raw.bytes.RawBytes.new misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple
      (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice core.clone.CloneU8)) s
      ⦃ r => cowList r.1 = s.val ⦄ := by
  apply WP.spec_mono (PKUtil.rawbytes_new_spec _ _ s (alloc.borrow.Cow.Borrowed s) rfl)
  intro r hr; rw [hr]; rfl

/-! ## Handshake round trip (pure) -/

theorem handshakeRead_enc (hs : Handshake) (hc : hs.Compatible) (tail : List U8)
    (ht : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true → tail = []) :
    handshakeRead (handshakeEnc hs ++ tail) = (some { hs with authDataLen := handshakeLenByte hs }, tail) ∧
      ¬ handshakePanics (handshakeEnc hs ++ tail) := by
  obtain ⟨hpv, hv, hcid, h1, hcl, hcoll, hst16, hst, hcu0, hcu, hmc, hsec, hs2, hpn, hpnn⟩ := hc
  have H := ConnHS.handshakeEnc_split hs tail h1
  obtain ⟨blk, rest, H⟩ := H
  have hbl := H.1
  have he := H.2.1
  have hrest := H.2.2.1
  have hcl' := H.2.2.2.1
  have hst' := H.2.2.2.2.1
  have hcu' := H.2.2.2.2.2.1
  have hlb := H.2.2.2.2.2.2.1
  have hcid' := H.2.2.2.2.2.2.2.1
  have hs1' := H.2.2.2.2.2.2.2.2.1
  have hcoll' := H.2.2.2.2.2.2.2.2.2.1
  have hlb1 := H.2.2.2.2.2.2.2.2.2.2.1
  have hmc' := H.2.2.2.2.2.2.2.2.2.2.2
  clear H
  have hlbv : handshakeLenByte hs < 128 := by
    unfold handshakeLenByte
    split
    · rcases hh : hs.scramble2 with _ | s
      · simp
      · have := hs2 s hh; rename_i hp; simp only [hp, ite_true] at this; simp; omega
    · omega
  have f0 : leNat ((blk.drop 0).take 4) = hs.connectionId := by
    rw [hcid', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hcid]
  have f13 : leNat ((blk.drop 13).take 2) = hs.capsLower := by
    rw [hcl', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hcl]
  have f15 : leNat ((blk.drop 15).take 1) = hs.collation := by
    rw [hcoll']; simp [leNat, byte_val]; omega
  have f16 : leNat ((blk.drop 16).take 2) = hs.status := by
    rw [hst', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hst16]
  have f18 : leNat ((blk.drop 18).take 2) * 2 ^ 16 = hs.capsUpper := by
    rw [hcu', PBUtil.leNat_leBytes]; omega
  have f20 : leNat ((blk.drop 20).take 1) = handshakeLenByte hs := by
    rw [hlb1]; simp [leNat, byte_val]; omega
  have hm63 : hs.mariadbCaps < 2 ^ 32 := by
    have : hs.mariadbCaps &&& mariadbCapabilitiesAll ≤ mariadbCapabilitiesAll := Nat.and_le_right
    rw [hmc] at this; simp [mariadbCapabilitiesAll] at this; omega
  have f27 : leNat ((blk.drop 27).take 4) &&& mariadbCapabilitiesAll = hs.mariadbCaps := by
    rw [hmc', PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hm63, hmc]
  have fpv : (byte hs.protocolVersion).val = hs.protocolVersion := by rw [byte_val]; omega
  have ht31 : (blk ++ rest).take 31 = blk := List.take_left' hbl
  have hd31 : (blk ++ rest).drop 31 = rest := List.drop_left' hbl
  have hl31 : ¬ (blk ++ rest).length < 31 := by simp; omega
  constructor
  · rw [he]
    unfold handshakeRead
    simp only [ConnHS.nulStrRead_nulStr _ _ hv, hl31, ↓reduceIte, ht31, hd31, f0, f13, f15, f16, f18, f20, f27, hst,
      reduceCtorEq, hs1', fpv]
    have hnul : ∀ n, hs.pluginName = some n → dropTrailingNul (nulStr n) = n := by
      intro n hn
      rw [CAUtil.nulStr_of_noNul n (hpnn n hn), CAUtil.dropTrailingNul_append_zero]
    rcases hS : hs.scramble2 with _ | sc <;> rcases hP : hs.pluginName with _ | n <;>
      simp only [hS, hP, Option.isSome_none, Option.isSome_some] at hsec hpn hrest hnul <;>
      simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, List.nil_append] at hrest
    · have hsf : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = false := by rw [← hsec]
      have hpf : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = false := by rw [← hpn]
      simp [hsf, hpf, hrest]
    · have hsf : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = false := by rw [← hsec]
      have hpf : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true := by rw [← hpn]
      have htl := ht hpf
      subst htl
      simp [hsf, hpf, hrest, hnul n rfl]
    all_goals
      have hsf : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true := by rw [← hsec]
      have hsl := hs2 sc hS
      have hlen : scramble2LenCrate (handshakeLenByte hs) = sc.length := by
        unfold handshakeLenByte scramble2LenCrate
        simp only [hS]
        split_ifs at * <;> omega
      have h247 : sc.take 247 = sc := List.take_of_length_le (by
        split at hsl <;> omega)
      rw [h247] at hrest
      rw [hlen, hrest]
    · have hpf : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = false := by rw [← hpn]
      simp [hsf, hpf]
    · have hpf : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true := by rw [← hpn]
      have htl := ht hpf
      subst htl
      simp [hsf, hpf, hnul n rfl]
  · rw [he]
    unfold handshakePanics
    simp only [ConnHS.nulStrRead_nulStr _ _ hv]
    rintro ⟨-, -, -, h5, -⟩
    rw [ConnHS.getD_app _ _ _ _ (by omega), hlb, byte_val] at h5
    omega

/-! ## Handshake response round trip (pure) -/

theorem scrambleRead_enc (caps : Nat) (k : ScrambleKind) (s r : List U8) (hk : k = scrambleKindFor caps)
    (hu8 : k = .u8 → s.length ≤ 255) (hnul : k = .nul → NoNul s) (h64 : k = .lenenc → s.length < 2 ^ 64) :
    scrambleRead caps (scrambleEnc k s ++ r) = (some (k, s), r) := by
  unfold scrambleRead
  rw [← hk]
  cases k with
  | lenenc => simp [scrambleEnc, Defs.checkedLenencStr_lenencStr _ _ (h64 rfl)]
  | u8 =>
    have hl := hu8 rfl
    simp only [scrambleEnc, List.cons_append, checkedLenPrefixed, readLE, List.length_cons]
    simp [List.take_of_length_le hl, leNat, byte_val, Nat.min_eq_left hl, Nat.mod_eq_of_lt (show s.length < 256 by omega)]
  | nul => simp [scrambleEnc, ConnHS.nulStrRead_nulStr _ _ (hnul rfl)]

theorem hsRespRead_enc (v : HsResp) (kvs : Option (List (List U8 × List U8))) (hc : v.Compatible kvs)
    (tail : List U8) (h64 : (hsRespEnc v kvs ++ tail).length < 2 ^ 64) :
    hsRespRead (hsRespEnc v kvs ++ tail) = (some (v, kvs), tail) := by
  obtain ⟨hcaps, hmp, hcoll, hmc, hu, hk, hu8, hnul, hdb, hdbn, hpn, hpnn, hkv⟩ := hc
  have hP : ¬ ((hsRespEnc v kvs ++ tail).length < 32) := by
    simp [hsRespEnc, PBUtil.length_leBytes]; omega
  have hm64 : v.mariadbCaps < 2 ^ 32 := by
    have : v.mariadbCaps &&& mariadbCapabilitiesAll ≤ mariadbCapabilitiesAll := Nat.and_le_right
    rw [hmc] at this; simp [mariadbCapabilitiesAll] at this; omega
  unfold hsRespRead
  simp only [hP, ↓reduceIte]
  unfold hsRespEnc
  simp only [leBytes, List.replicate, List.cons_append, List.nil_append, List.append_assoc]
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  rw [leNat_bytes4, leNat_bytes4, leNat_bytes4, leNat_bytes1, Nat.mod_eq_of_lt hcaps, Nat.mod_eq_of_lt hmp,
    Nat.mod_eq_of_lt hcoll, Nat.mod_eq_of_lt hm64, hmc]
  rw [ConnHS.nulStrRead_nulStr _ _ hu]
  simp only
  have hlen := h64
  simp only [hsRespEnc, List.length_append] at hlen
  rw [scrambleRead_enc v.caps v.scrambleKind v.scramble _ hk hu8 hnul (by
    intro hl; rw [hl] at hlen; simp [scrambleEnc, lenencStr] at hlen; omega)]
  simp only
  have hA : ∀ kv, kvs = some kv → (attrsEnc kv).length < 2 ^ 64 := by
    intro kv hkv; subst hkv; simp [hsRespEnc] at h64; omega
  have hdz : ∀ (n r : List U8), (n ++ [byte 0] ++ r).drop (n.length + 1) = r := by
    intro n r; simp [List.drop_append]
  have hbz : ∀ n r, NoNul n → beforeZero (n ++ [byte 0] ++ r) = n := by
    intro n r hn; rw [List.append_assoc, List.singleton_append]; exact beforeZero_append_zero n r hn
  rcases hD : v.db with _ | d <;> rcases hPn : v.pluginName with _ | n <;> rcases hK : kvs with _ | kv <;>
    simp only [hD, hPn, hK, Option.isSome_none, Option.isSome_some] at hdb hpn hkv hlen ⊢
  all_goals
    simp only [← hdb, ← hpn, ← hkv, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    (try rw [ConnHS.nulStrRead_nulStr _ _ (hdbn _ hD)])
    (try simp only)
    (try simp only [hbz _ _ (hpnn _ hPn), hdz])
    (try rw [Defs.connectAttrsRead_attrsEnc _ _ (hA _ hK)])
    cases v
    simp_all

/-! ## Handshake response reading steps -/

theorem flag_pos_iff (flags : U32) (c : constants.CapabilityFlags) (i : U32) (k : Nat)
    (hc : c.val = 2 ^ k) (hi : i.val = (flags &&& c).val) :
    (i > 0#u32 ↔ hasFlag flags.val (2 ^ k) = true) := by
  have : i = flags &&& c := UScalar.eq_of_val_eq hi
  rw [this]; exact u32_and_pos_iff flags c k hc

theorem scramble_step (h64 : Target64) (flags : U32) (buf : io.ParseBuf) :
    packets.parse_scramble_buf flags buf ⦃ r rest =>
      ((okPart r).map scrambleView, rest.val) = scrambleRead flags.val buf.val ⦄ := by
  unfold packets.parse_scramble_buf scrambleRead scrambleKindFor
  have hlv : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA).val = 2 ^ 21 := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA]
  have hsv : (constants.CapabilityFlags.CLIENT_SECURE_CONNECTION).val = 2 ^ 15 := by
    simp [constants.CapabilityFlags.CLIENT_SECURE_CONNECTION]
  step*
  · have hf := (flag_pos_iff flags i i1 21 (by rw [i_post, hlv]) i1_post).1 (by assumption)
    step with parse_lenenc_bytes_spec h64 as ⟨r, b, hr⟩
    simp only [CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA, hf, ite_true]
    rw [← hr]
    cases r <;> simp [okPart, scrambleView]
  · have hf1 := (flag_pos_iff flags i i1 21 (by rw [i_post, hlv]) i1_post).not.1 (by assumption)
    have hf2 := (flag_pos_iff flags i2 i3 15 (by rw [i2_post, hsv]) i3_post).1 (by assumption)
    step with parse_u8bytes_spec as ⟨r, b, hr⟩
    simp only [CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA, CLIENT_SECURE_CONNECTION, hf1, hf2, ite_true,
      Bool.false_eq_true, ite_false]
    rw [← hr]
    cases r <;> simp [okPart, scrambleView]
  · have hf1 := (flag_pos_iff flags i i1 21 (by rw [i_post, hlv]) i1_post).not.1 (by assumption)
    have hf2 := (flag_pos_iff flags i2 i3 15 (by rw [i2_post, hsv]) i3_post).not.1 (by assumption)
    step with CAUtil.parse_null_bytes_spec as ⟨r, b, hr⟩
    simp only [CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA, CLIENT_SECURE_CONNECTION, hf1, hf2,
      Bool.false_eq_true, ite_false]
    rw [← hr]
    cases r <;> simp [okPart, scrambleView]

/-- The database step of `hsRespRead`. -/
def dbRead (caps : Nat) (bs : List U8) : Option (Option (List U8)) × List U8 :=
  if hasFlag caps CLIENT_CONNECT_WITH_DB then
    match nulStrRead bs with
    | (none, r) => (none, r)
    | (some d, r) => (some (some d), r)
  else (some none, bs)

/-- The plugin step of `hsRespRead`. -/
def hrPnRead (caps : Nat) (bs : List U8) : Option (List U8) × List U8 :=
  if hasFlag caps CLIENT_PLUGIN_AUTH then (some (beforeZero bs), bs.drop ((beforeZero bs).length + 1))
  else (none, bs)

theorem db_step (flags : U32) (buf : io.ParseBuf) :
    packets.parse_handshake_response_db_name flags buf ⦃ r rest =>
      ((okPart r).map (Option.map (fun rb => cowList rb.1)), rest.val) = dbRead flags.val buf.val ⦄ := by
  unfold packets.parse_handshake_response_db_name dbRead
  have hdv : (constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB).val = 2 ^ 3 := by
    simp [constants.CapabilityFlags.CLIENT_CONNECT_WITH_DB]
  step*
  · have hf := (flag_pos_iff flags i i1 3 (by rw [i_post, hdv]) i1_post).1 (by assumption)
    step with CAUtil.parse_null_bytes_spec as ⟨r, b, hr⟩
    simp only [CLIENT_CONNECT_WITH_DB, hf, ite_true]
    rw [← hr]
    cases r <;> simp [okPart]
  · have hf := (flag_pos_iff flags i i1 3 (by rw [i_post, hdv]) i1_post).not.1 (by assumption)
    have hf' : hasFlag flags.val 8 = false := by simpa using hf
    simp only [CLIENT_CONNECT_WITH_DB]
    simp [hf', okPart]

theorem hr_plugin_step (flags : U32) (buf : io.ParseBuf) :
    packets.parse_handshake_response_auth_plugin flags buf ⦃ o rest =>
      (o.map authPluginName, rest.val) = hrPnRead flags.val buf.val ∧ ∀ p, o = some p → PluginCanonical p ⦄ := by
  unfold packets.parse_handshake_response_auth_plugin hrPnRead
  have hpv : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH).val = 2 ^ 19 := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH]
  step*
  · have hf := (flag_pos_iff flags i i1 19 (by rw [i_post, hpv]) i1_post).1 (by assumption)
    step with io.ParseBuf.eat_null_str_spec as ⟨s0, b1, hs0, hb1⟩
    step with packets.AuthPlugin.from_bytes_spec as ⟨ap, hap⟩
    have hn := (PluginFromBytes.named hap)
    rw [hs0, CAUtil.dropTrailingNul_of_noNul _ (CAUtil.noNul_beforeZero _)] at hn
    simp only [CLIENT_PLUGIN_AUTH, hf, ite_true]
    refine ⟨?_, ?_⟩
    · simp [IsPluginNamed.authPluginName hn.1, hb1]
    · intro p hp; cases hp; exact hn.2
  · have hf := (flag_pos_iff flags i i1 19 (by rw [i_post, hpv]) i1_post).not.1 (by assumption)
    have hf' : hasFlag flags.val 524288 = false := by simpa using hf
    simp only [CLIENT_PLUGIN_AUTH]
    simp [hf']

theorem hsRespRead_eq (bs : List U8) : hsRespRead bs =
    if bs.length < 32 then (none, bs)
    else
      let f := bs.take 32
      let field (i k : Nat) : Nat := leNat ((f.drop i).take k)
      let caps := field 0 4
      match nulStrRead (bs.drop 32) with
      | (none, r) => (none, r)
      | (some user, r1) =>
        match scrambleRead caps r1 with
        | (none, r) => (none, r)
        | (some (k, s), r2) =>
          match dbRead caps r2 with
          | (none, r) => (none, r)
          | (some db, r3) =>
            match CAUtil.attRead caps (hrPnRead caps r3).2 with
            | (none, r) => (none, r)
            | (some kvs, r5) =>
              (some ({ caps := caps, maxPacket := field 4 4, collation := field 8 1,
                       mariadbCaps := field 28 4 &&& mariadbCapabilitiesAll, user := user,
                       scrambleKind := k, scramble := s, db := db,
                       pluginName := (hrPnRead caps r3).1 }, kvs), r5) := by
  unfold hsRespRead
  rfl

/-! ## Failure chains -/

theorem branch_ok_spec {T E : Type} (x : T) :
    CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result T E) ⦃ c =>
      c = core.ops.control_flow.ControlFlow.Continue x ⦄ := by
  simp [CAUtil.branch_ok]

theorem i8_sub_fail (x y : I8) (h : ¬ (-128 ≤ x.val - y.val ∧ x.val - y.val ≤ 127)) :
    x - y = fail .integerOverflow := by
  show IScalar.tryMk .I8 (x.val - y.val) = _
  unfold IScalar.tryMk IScalar.tryMkOpt
  rw [dite_eq_right_iff.mpr]
  · rfl
  · intro hc; exfalso; apply h
    have := IScalar.check_bounds_imp_inBounds hc
    simp [IScalar.inBounds, IScalarTy.numBits] at this
    omega

end mysql_common.ConnHSUtil
