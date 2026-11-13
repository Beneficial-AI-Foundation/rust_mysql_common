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

end mysql_common.ConnHSUtil
