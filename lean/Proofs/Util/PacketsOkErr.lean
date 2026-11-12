import Defs
import Proofs.Util.ParseBuf
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.ParseBuf
import Proofs.Misc.Raw.Array
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU24
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.LenEnc
import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Const.Const
import Proofs.Constants.StatusFlags
import Proofs.Constants.CapabilityFlags

/-! Helper lemmas for the OK/EOF/ERR packet proofs (`Proofs/Packets/{OkPacket,OkPacketKind,
OkPacketDeserializer,ErrPacket,ServerError,SqlState,ProgressReport}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common.PKUtil

theorem parse_usize_spec (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.parse io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf n ⦃ r rest =>
      if n.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])]
  exact deserialize_usize_ok n buf

theorem parse_unchecked_status_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags
      constants.UnknownStatusFlags.Insts.CoreErrorError) buf () ⦃ r rest =>
      (okPart r).map (fun c => c.1.val) = statusRead (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
    constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags
    constants.UnknownStatusFlags.Insts.CoreErrorError buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2)
    (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h)
    (fun p o => o.map (fun c : constants.StatusFlags => c.val) = statusRead p.val)
    (fun p => by
      apply WP.spec_mono (constants.StatusFlags.Insts.CoreConvertTryFromU16UnknownStatusFlags.try_from_spec p)
      intro r hr
      subst hr
      unfold statusRead
      split_ifs <;> simp_all [okPart])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨ho, hrest⟩, hm⟩
  refine ⟨?_, hrest⟩
  cases o with
  | none => simp at ho
  | some p =>
    simp at ho hm
    rw [← ho]
    exact hm

theorem parse_unchecked_leu16_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2)
    (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

theorem parse_lenenc_bytes_spec (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = checkedLenencStr buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = checkedLenencStr buf.val)
    (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf h64)

theorem parse_eof_bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      (okPart r).map (fun rb => cowList rb.1) = some buf.val ∧ rest.val = [] ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => o = some buf.val ∧ rest.val = [])
    (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

theorem caps_contains_spec (caps other : constants.CapabilityFlags) :
    constants.CapabilityFlags.contains caps other ⦃ b => b = hasFlag caps.val other.val ⦄ := by
  unfold constants.CapabilityFlags.contains hasFlag
  step*

theorem status_contains_spec (s other : constants.StatusFlags) :
    constants.StatusFlags.contains s other ⦃ b => b = hasFlag s.val other.val ⦄ := by
  unfold constants.StatusFlags.contains hasFlag
  step*

/-! ## Small evaluation lemmas (as step specs: the translation's `ok (x, ())` is typed at
`P × Unit` rather than `RawInt T P`, so rewriting with `bind_ok` does not fire) -/

@[step] theorem rawint_new_spec {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x ⦃ r => r.1 = x ⦄ := by
  have e : misc.raw.int.RawInt.new inst x = ok (x, ()) := rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem rawint_deref_spec {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : misc.raw.int.RawInt T P) :
    misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref inst x ⦃ v => v = x.1 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref inst x = ok x.1 := rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem const_deref_spec {T U : Type} (x : misc.raw._const.Const T U) :
    misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref x ⦃ v => v = x.1 ⦄ := by
  have e : misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref x = ok x.1 := rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem rawbytes_new_cow_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    misc.raw.bytes.RawBytes.new inst (core.convert.IntoFrom (core.convert.FromSame _)) c ⦃ r => r.1 = c ⦄ := by
  have e : misc.raw.bytes.RawBytes.new inst (core.convert.IntoFrom (core.convert.FromSame _)) c = ok (c, ()) := by
    simp [misc.raw.bytes.RawBytes.new]; try rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem rawbytes_default_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) (d : core.default.Default T) :
    misc.raw.bytes.RawBytes.Insts.CoreDefaultDefault.default inst d ⦃ r => cowList r.1 = [] ⦄ := by
  have e : misc.raw.bytes.RawBytes.Insts.CoreDefaultDefault.default inst d =
      ok (alloc.borrow.Cow.Owned (alloc.vec.Vec.new U8), ()) := rfl
  rw [e]; exact (WP.spec_ok _).mpr (by simp [cowList, alloc.vec.Vec.new])

@[step] theorem empty_index_spec :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice U8))
      (Std.Array.empty U8) () ⦃ s => s.val = [] ⦄ := by
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index, Array.to_slice]
  rfl

@[simp] theorem cowList_borrowed (s : Slice U8) : cowList (alloc.borrow.Cow.Borrowed s : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) = s.val := rfl

@[simp] theorem cowList_owned (v : alloc.vec.Vec U8) : cowList (alloc.borrow.Cow.Owned v : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) = v.val := rfl

@[simp] theorem okPart_Ok {T E : Type} (x : T) : okPart (core.result.Result.Ok x : core.result.Result T E) = some x := rfl
@[simp] theorem okPart_Err {T E : Type} (e : E) : okPart (core.result.Result.Err e : core.result.Result T E) = none := rfl

/-! ## Flag constants -/

@[simp] theorem CLIENT_SESSION_TRACK_val : constants.CapabilityFlags.CLIENT_SESSION_TRACK.val = CLIENT_SESSION_TRACK := by
  simp [constants.CapabilityFlags.CLIENT_SESSION_TRACK, CLIENT_SESSION_TRACK]

@[simp] theorem CLIENT_PROTOCOL_41_val : constants.CapabilityFlags.CLIENT_PROTOCOL_41.val = CLIENT_PROTOCOL_41 := by
  simp [constants.CapabilityFlags.CLIENT_PROTOCOL_41, CLIENT_PROTOCOL_41]

@[simp] theorem CLIENT_PROGRESS_OBSOLETE_val : constants.CapabilityFlags.CLIENT_PROGRESS_OBSOLETE.val = CLIENT_PROGRESS_OBSOLETE := by
  simp [constants.CapabilityFlags.CLIENT_PROGRESS_OBSOLETE, CLIENT_PROGRESS_OBSOLETE]

@[simp] theorem SERVER_SESSION_STATE_CHANGED_val : constants.StatusFlags.SERVER_SESSION_STATE_CHANGED.val = SERVER_SESSION_STATE_CHANGED := by
  simp [constants.StatusFlags.SERVER_SESSION_STATE_CHANGED, SERVER_SESSION_STATE_CHANGED]

/-! ## `RawBytes` with `MAX_LEN = usize::MAX` -/

theorem cowList_length_le (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    (cowList c).length ≤ Usize.max := by
  cases c <;> simp [cowList]

theorem rawbytes_as_bytes_full {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (hmv : m.val = Usize.max) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.as_bytes inst self ⦃ s => s.val = cowList self.1 ⦄ := by
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec inst m hm self)
  intro s hs
  rw [hs, List.take_of_length_le]
  rw [hmv]; exact cowList_length_le _

theorem rawbytes_is_empty_full {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (hmv : m.val = Usize.max) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.is_empty inst self ⦃ b => (b ↔ cowList self.1 = []) ⦄ := by
  apply WP.spec_mono (misc.raw.bytes.RawBytes.is_empty_spec inst m hm self)
  intro b hb
  rw [hb]
  have : 0 < Usize.max := by scalar_tac
  constructor
  · intro h; rw [← List.length_eq_zero_iff]; omega
  · intro h; simp [h]

@[step] theorem lenenc_as_bytes_spec (self : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple self
      ⦃ s => s.val = cowList self.1 ⦄ :=
  rawbytes_as_bytes_full _ _ rfl misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec self

@[step] theorem eof_as_bytes_spec (self : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple self
      ⦃ s => s.val = cowList self.1 ⦄ :=
  rawbytes_as_bytes_full _ _ rfl misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec self

@[step] theorem lenenc_is_empty_spec (self : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.is_empty misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple self
      ⦃ b => (b ↔ cowList self.1 = []) ⦄ :=
  rawbytes_is_empty_full _ _ rfl misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec self

@[step] theorem rawbytes_into_owned_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.into_owned inst self ⦃ r => cowList r.1 = cowList self.1 ⦄ := by
  obtain ⟨c, _⟩ := self
  unfold misc.raw.bytes.RawBytes.into_owned misc.raw.cow_into_vec
  cases c with
  | Borrowed s =>
    step*
    subst s_post
    exact (WP.spec_ok _).mpr (by simp [cowList]; try rfl)
  | Owned v =>
    step*

@[step] theorem non_empty_spec (self : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    packets.non_empty misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple self
      ⦃ o => o.map (fun rb => cowList rb.1) = if cowList self.1 = [] then none else some (cowList self.1) ⦄ := by
  unfold packets.non_empty
  step* <;> simp_all

end mysql_common.PKUtil
