import Defs
import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.ConstU32
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Skip
import Proofs.Constants.ColumnType
import Proofs.Constants.ColumnFlags
import Proofs.Defs.LemmasCF
import Proofs.Util.ParseBuf

/-! Helper lemmas for the `Column`, `ColumnMeta`, `NullBitmap` and `ComStmtExecuteRequest` proofs
(`Proofs/Packets/{Column,ColumnMeta,NullBitmap,ComStmtExecuteRequest,ComStmtExecuteRequestBuilder}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.PCSUtil

theorem cowList_length_le {T : Type} (c : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) :
    (cowList c).length ≤ Usize.max := by
  cases c <;> simp [cowList]

theorem byte_eq_self (x : U8) : byte x.val = x := by
  cases x; simp [byte, UScalar.val]

theorem byte_eq_of_val (x : U8) (n : Nat) (h : x.val = n) : x = byte n := by
  rw [← h, byte_eq_self]

theorem lenenc_MAX_LEN :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max :=
  misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec

/-- `as_bytes` of a length-encoded `RawBytes`: all the bytes. -/
theorem lenenc_as_bytes (rb : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = cowList rb.1 ⦄ := by
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ _ rfl rb)
  intro s hs
  rw [hs, lenenc_MAX_LEN]
  exact List.take_of_length_le (cowList_length_le _)

end mysql_common.PCSUtil

namespace mysql_common.PCSUtil

/-- One length-encoded `RawBytes` read: `checkedLenencStr`. -/
theorem lenenc_raw_deserialize (h64 : Target64) (buf : io.ParseBuf) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf ⦃ r rest =>
      (okPart r).map (fun rb => cowList rb.1) = (checkedLenencStr buf.val).1 ∧
      rest.val = (checkedLenencStr buf.val).2 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ _ _
    (fun o rest => o = (checkedLenencStr buf.val).1 ∧ rest.val = (checkedLenencStr buf.val).2)
  apply WP.spec_mono (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf h64)
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'] at h ⊢
  rw [← h]; simp

/-- `?` on a `Result`, in a form `simp_all` can use once the branch taken is known. -/
@[step]
theorem branch_spec' {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r ⦃ cf =>
      (∀ v, cf = .Continue v → r = .Ok v) ∧
      (∀ res, cf = .Break res → ∃ e, r = .Err e ∧ res = .Err e) ⦄ := by
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- One length-encoded `RawBytes` read, as an equation on `checkedLenencStr`. -/
@[step]
theorem lenenc_raw_deserialize' (h64 : Target64) (buf : io.ParseBuf) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf ⦃ r rest =>
      checkedLenencStr buf.val = ((okPart r).map (fun rb => cowList rb.1), rest.val) ⦄ := by
  apply WP.spec_mono (lenenc_raw_deserialize h64 buf)
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  simp only [WP.uncurry'] at h1 h2 ⊢
  rw [h1, h2]

/-- `into_owned` of a length-encoded `RawBytes`: the same bytes. -/
theorem raw_into_owned {T C : Type} (inst : misc.raw.bytes.BytesRepr T C) (rb : misc.raw.bytes.RawBytes T C) :
    misc.raw.bytes.RawBytes.into_owned inst rb ⦃ rb' => cowList rb'.1 = cowList rb.1 ⦄ := by
  have e : misc.raw.bytes.RawBytes.into_owned inst rb =
      (misc.raw.cow_into_vec core.clone.CloneU8 rb.1 >>= fun v =>
        ok ((alloc.borrow.Cow.Owned v, ()) : misc.raw.bytes.RawBytes T C)) := rfl
  rw [e]
  generalize rb.1 = c
  unfold misc.raw.cow_into_vec
  cases c with
  | Borrowed s =>
    simp only
    apply WP.spec_bind (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (by simp))
    intro v hv
    apply (WP.spec_ok ((alloc.borrow.Cow.Owned v, ()) : misc.raw.bytes.RawBytes T C)).mpr
    show v.val = s.val
    subst hv; rfl
  | Owned v =>
    simp only [bind_tc_ok]
    apply (WP.spec_ok ((alloc.borrow.Cow.Owned v, ()) : misc.raw.bytes.RawBytes T C)).mpr
    show cowList (alloc.borrow.Cow.Owned v) = cowList (alloc.borrow.Cow.Owned v)
    rfl

/-- Serializing a length-encoded `RawBytes`: appends the length-encoded string. -/
@[step]
theorem lenenc_raw_serialize (rb : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr (cowList rb.1)).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf
      ⦃ buf' => buf'.val = buf.val ++ lenencStr (cowList rb.1) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  rw [← hs] at h ⊢
  exact misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf h

/-! ## Serialization step lemmas -/

@[step]
theorem rawint_u32_serialize (x : misc.raw.int.RawInt misc.raw.int.LeU32 U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ b => b.val = buf.val ++ leBytes 4 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

@[step]
theorem rawint_u16_serialize (x : misc.raw.int.RawInt misc.raw.int.LeU16 U16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

@[step]
theorem rawint_u8_serialize (x : misc.raw.int.RawInt U8 U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ b => b.val = buf.val ++ [byte x.1.val] ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq, byte_eq_self]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

@[step]
theorem const_coltype_serialize (x : misc.raw._const.Const constants.ColumnType U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.ColumnType.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromColumnType) U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ b => b.val = buf.val ++ [byte (columnTypeCode x.1)] ⦄ := by
  obtain ⟨p, hp, hpv⟩ := mysql_common.PBUtil.spec_eq_ok (U8.Insts.CoreConvertFromColumnType.from_spec x.1)
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ p hp, ← hpv, byte_eq_self]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

@[step]
theorem const_colflags_serialize (x : misc.raw._const.Const constants.ColumnFlags misc.raw.int.LeU16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.ColumnFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U16.Insts.CoreConvertFromColumnFlags)
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1
    (U16.Insts.CoreConvertFromColumnFlags.from_eq _)]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

@[step]
theorem constu8_serialize {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [N] ⦄ :=
  misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec self buf h

@[step]
theorem constu32_serialize {T : Type} {N : U32} (self : misc.raw.int.ConstU32 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 N.val ⦄ :=
  misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize_spec self buf h

@[step]
theorem skip_serialize {LEN : Usize} (self : misc.raw.Skip LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ List.replicate LEN.val (byte 0) ⦄ :=
  misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec self buf h

/-! ## Bits -/

theorem and_two_pow (n k : Nat) : n &&& 2 ^ k = if n.testBit k then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : k = j
  · subst hj; split <;> simp_all [Nat.testBit_two_pow]
  · split <;> simp [Nat.testBit_two_pow, hj]

theorem or_two_pow_testBit (n k j : Nat) : (n ||| 2 ^ k).testBit j = (n.testBit j || decide (k = j)) := by
  simp [Nat.testBit_two_pow]

theorem u8_not_testBit (y : U8) (j : Nat) (hj : j < 8) : (~~~y).val.testBit j = !(y.val.testBit j) := by
  show (~~~y.bv).toNat.testBit j = !(y.bv.toNat.testBit j)
  rw [BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]; simp [hj]

theorem bitAt_set (l : List U8) (k : Nat) (y : U8) (pos : Nat) (hk : k < l.length) :
    bitAt (l.set k y) pos = if pos / 8 = k then y.val.testBit (pos % 8) else bitAt l pos := by
  unfold bitAt
  split_ifs with h
  · subst h; simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem bitAt_of_lt (l : List U8) (pos : Nat) (h : pos / 8 < l.length) :
    bitAt l pos = (l[pos / 8]'h).val.testBit (pos % 8) := by
  simp [bitAt, List.getD_eq_getElem?_getD, h]

theorem pos_eq_iff (pos n : Nat) : pos = n ↔ (pos / 8 = n / 8 ∧ pos % 8 = n % 8) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; omega

/-! ## `put_slice` -/

@[step]
theorem put_slice_ok (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice v s ⦃ v' => v'.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp only [h, _root_.dite_true]
  step*

end mysql_common.PCSUtil
