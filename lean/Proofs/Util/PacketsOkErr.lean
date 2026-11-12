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

/-! ## Pure lemmas about the OK/EOF readers and encoders -/

theorem slice_len_lt (s : Slice U8) : s.val.length < 2 ^ 64 := by
  have h1 : s.val.length ≤ Usize.max := by scalar_tac
  have h2 : Usize.max < 2 ^ 64 := by
    rw [Usize.max_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all
  omega


theorem checkedLenencStr_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s ++ t) = (some s, t) := by
  unfold checkedLenencStr lenencStr
  rw [List.append_assoc, checkedLenencInt_lenencInt _ _ hs]
  simp

theorem lenencInt_ne_nil (n : Nat) : lenencInt n ≠ [] := by
  unfold lenencInt; split_ifs <;> simp

theorem lenencInt_head_pos (n : Nat) (hn : 0 < n) : ∃ x t, lenencInt n = x :: t ∧ 0 < x.val := by
  unfold lenencInt
  split_ifs with h1 h2 h3
  · refine ⟨_, _, rfl, ?_⟩; rw [byte_val]; omega
  · refine ⟨_, _, rfl, ?_⟩; rw [byte_val]; omega
  · refine ⟨_, _, rfl, ?_⟩; rw [byte_val]; omega
  · refine ⟨_, _, rfl, ?_⟩; rw [byte_val]; omega

theorem leNat_take_leBytes (k n : Nat) (t : List U8) (hn : n < 2 ^ (8 * k)) :
    leNat ((leBytes k n ++ t).take k) = n := by
  rw [List.take_append_of_le_length (by rw [length_leBytes]), List.take_of_length_le (by rw [length_leBytes]),
    leNat_leBytes, Nat.mod_eq_of_lt hn]

theorem okStatusRead_enc (s w : Nat) (t : List U8) (hs : s < 2 ^ 16) (hw : w < 2 ^ 16)
    (hsk : statusRead s = some s) :
    okStatusRead (leBytes 2 s ++ leBytes 2 w ++ t) = (some (s, w), t) := by
  unfold okStatusRead
  have l1 := length_leBytes 2 s
  have l2 := length_leBytes 2 w
  rw [ite_eq_right (by simp [l1, l2]; omega)]
  rw [List.append_assoc, leNat_take_leBytes 2 s _ hs]
  rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    leNat_take_leBytes 2 w _ hw, hsk]
  rw [← List.append_assoc, List.drop_left' (by simp [l1, l2])]
  simp

theorem checkedLenencStr_lenencStr' (s : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s) = (some s, []) := by
  have := checkedLenencStr_lenencStr s [] hs
  simpa using this

theorem lenencStr_ne_nil (s : List U8) : lenencStr s ≠ [] := by
  unfold lenencStr; simp [lenencInt_ne_nil]

/-- The tail of `okPacketEnc` (after the warnings). -/
def okTailEnc (caps : Nat) (compact : Bool) (b : OkBody) : List U8 :=
  if hasFlag caps CLIENT_SESSION_TRACK then
    (if compact ∧ b.info = [] ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED = false then []
     else lenencStr b.info)
      ++ (if hasFlag b.status SERVER_SESSION_STATE_CHANGED then lenencStr b.sessionStateInfo else [])
  else if b.info = [] then [] else lenencStr b.info

theorem okPacketEnc_eq (header caps : Nat) (compact : Bool) (b : OkBody) :
    okPacketEnc header caps compact b =
      byte header :: (lenencInt b.affectedRows ++ (lenencInt b.lastInsertId ++
        (leBytes 2 b.status ++ leBytes 2 b.warnings ++ okTailEnc caps compact b))) := by
  simp [okPacketEnc, okTailEnc]

theorem okTailRead_enc (caps : Nat) (compact : Bool) (b : OkBody)
    (hi : b.info.length < 2 ^ 64) (hs : b.sessionStateInfo.length < 2 ^ 64)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = []) :
    okTailRead caps b.status (okTailEnc caps compact b) = (some (b.info, b.sessionStateInfo), []) := by
  unfold okTailEnc
  cases hc : hasFlag caps CLIENT_SESSION_TRACK <;> cases hsf : hasFlag b.status SERVER_SESSION_STATE_CHANGED <;>
    simp only [hc, hsf, and_true, and_false, false_or, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, List.append_nil] at hssi ⊢
  · -- no session track, no state change
    by_cases hinf : b.info = []
    · simp [hinf, okTailRead, hssi]
    · simp only [hinf, ite_false]
      obtain ⟨x, t, hxt, hx⟩ := lenencInt_head_pos b.info.length (List.length_pos_iff.mpr hinf)
      have hl : lenencStr b.info = x :: (t ++ b.info) := by simp [lenencStr, hxt]
      unfold okTailRead
      rw [ite_eq_right (by simp [hc])]
      rw [hl]; simp only [hx, ite_true]; rw [← hl, checkedLenencStr_lenencStr' _ hi, hssi]
  · by_cases hinf : b.info = []
    · simp [hinf, okTailRead, hssi]
    · simp only [hinf, ite_false]
      obtain ⟨x, t, hxt, hx⟩ := lenencInt_head_pos b.info.length (List.length_pos_iff.mpr hinf)
      have hl : lenencStr b.info = x :: (t ++ b.info) := by simp [lenencStr, hxt]
      unfold okTailRead
      rw [ite_eq_right (by simp [hc])]
      rw [hl]; simp only [hx, ite_true]; rw [← hl, checkedLenencStr_lenencStr' _ hi, hssi]
  · split_ifs with hcomp
    · obtain ⟨hcomp, hinf⟩ := hcomp
      simp [hinf, okTailRead, hssi]
    · unfold okTailRead
      rw [ite_eq_left ⟨by simp [hc], by simp [lenencStr_ne_nil]⟩]
      rw [checkedLenencStr_lenencStr' _ hi]
      simp [hsf, hssi]
  · unfold okTailRead
    rw [ite_eq_left ⟨by simp [hc], by simp [lenencStr_ne_nil]⟩]
    rw [checkedLenencStr_lenencStr _ _ hi]
    simp only [hsf, ite_true]
    rw [checkedLenencStr_lenencStr' _ hs]

theorem okBodyRead_enc (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hi : b.info.length < 2 ^ 64) (hs : b.sessionStateInfo.length < 2 ^ 64)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = []) :
    okBodyRead caps (lenencInt b.affectedRows ++ (lenencInt b.lastInsertId ++
        (leBytes 2 b.status ++ leBytes 2 b.warnings ++ okTailEnc caps compact b))) = (some b, []) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  unfold okBodyRead
  rw [checkedLenencInt_lenencInt _ _ h1]
  simp only
  rw [checkedLenencInt_lenencInt _ _ h2]
  simp only
  rw [okStatusRead_enc _ _ _ h3 h5 h4]
  simp only
  rw [okTailRead_enc _ _ _ hi hs hssi]

theorem info_length_le (caps : Nat) (compact : Bool) (b : OkBody) :
    b.info.length ≤ (okTailEnc caps compact b).length := by
  unfold okTailEnc lenencStr
  split_ifs <;> simp_all; omega

theorem ssi_length_le (caps : Nat) (compact : Bool) (b : OkBody)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = []) :
    b.sessionStateInfo.length ≤ (okTailEnc caps compact b).length := by
  rcases hssi with ⟨hc, hs⟩ | h
  · unfold okTailEnc lenencStr
    simp [hc, hs]; omega
  · simp [h]

theorem okPacketRead_commonOk (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hlen : (okPacketEnc 0x00 caps compact b).length < 2 ^ 64) :
    okPacketRead .commonOk caps (okPacketEnc 0x00 caps compact b) = (some b.toPkt, []) := by
  have hl := hlen
  rw [okPacketEnc_eq] at hl ⊢
  simp only [List.length_cons, List.length_append] at hl
  have hi := info_length_le caps compact b
  have hs := ssi_length_le caps compact b hssi
  unfold okPacketRead
  simp only [byte_val, OkKind.header, OkKind.bodyRead]
  rw [okBodyRead_enc caps compact b hb (by omega) (by omega) hssi]
  simp

theorem okPacketRead_rs (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hlen : (okPacketEnc 0xFE caps compact b).length < 2 ^ 64) :
    okPacketRead .resultSetTerminator caps (okPacketEnc 0xFE caps compact b) =
      (some { b with affectedRows := 0, lastInsertId := 0 }.toPkt, []) := by
  have hl := hlen
  rw [okPacketEnc_eq] at hl ⊢
  simp only [List.length_cons, List.length_append] at hl
  have hi := info_length_le caps compact b
  have hs := ssi_length_le caps compact b hssi
  unfold okPacketRead
  simp only [byte_val, OkKind.header, OkKind.bodyRead, rsTerminatorBodyRead]
  rw [okBodyRead_enc caps compact b hb (by omega) (by omega) hssi]
  simp

theorem eofBodyRead_enc (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16) (hsk : statusRead s = some s)
    (tail : List U8) :
    eofBodyRead (leBytes 2 w ++ leBytes 2 s ++ tail) = (some ⟨0, 0, s, w, [], []⟩, tail) := by
  unfold eofBodyRead
  have l1 := length_leBytes 2 s
  have l2 := length_leBytes 2 w
  rw [ite_eq_right (by simp [l1, l2]; omega)]
  rw [List.append_assoc, leNat_take_leBytes 2 w _ hw]
  rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    leNat_take_leBytes 2 s _ hs, hsk]
  rw [← List.append_assoc, List.drop_left' (by simp [l1, l2])]
  simp

theorem okPacketRead_eof (k : OkKind) (hk : k = .oldEof ∨ k = .networkStreamTerminator) (caps : Nat)
    (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16) (hsk : statusRead s = some s) (tail : List U8) :
    okPacketRead k caps (eofPacketEnc w s ++ tail) = (some ⟨0, none, s, w, none, none⟩, tail) := by
  unfold eofPacketEnc
  rcases hk with rfl | rfl <;>
  · simp only [List.cons_append, okPacketRead, byte_val, OkKind.header, OkKind.bodyRead]
    rw [eofBodyRead_enc w s hw hs hsk]
    simp [OkBody.toPkt]

/-! ## Fixed-size readers, `put_u8`, `RawBytes::new` -/

theorem parse_array_spec (n : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple n) buf () ⦃ r rest =>
      if n.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs : (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple n).SIZE = ok (some n) := by
    simp [ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  by_cases hl : n.val ≤ buf.length
  · simp only [hl, ite_true]
    apply io.ParseBuf.parse_of_size _ _ _ n hs hl (fun o => o.map (·.val) = some (buf.val.take n.val))
    intro sub hsub
    apply WP.spec_mono (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec n sub
      (by simp only [Slice.length, hsub, List.length_take]; simp only [Slice.length] at hl; omega))
    rintro ⟨r, _⟩ ⟨h1, _⟩
    simp only [WP.uncurry'_pair]
    rw [h1, hsub]; simp
  · simp only [hl, ite_false]
    exact io.ParseBuf.parse_of_size_short _ _ _ n hs (by omega)

theorem parse_unchecked_u8_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec U8.Insts.Mysql_commonMiscRawIntIntReprU8 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1)
    (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

theorem parse_unchecked_leu24_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3)
    (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

theorem put_u8_spec (buf : alloc.vec.Vec U8) (x : U8) (h : buf.length + 1 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 buf x ⦃ buf' => buf'.val = buf.val ++ [x] ⦄ :=
  U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec x buf h

@[step] theorem rawbytes_new_spec {T T2 Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (into : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (text : T2)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into text = ok c) :
    misc.raw.bytes.RawBytes.new inst into text ⦃ r => r.1 = c ⦄ := by
  rw [misc.raw.bytes.RawBytes.new_eq inst into text c h]
  exact (WP.spec_ok _).mpr rfl

theorem byte_val_self (x : U8) : byte x.val = x := by
  unfold byte; cases x; simp [UScalar.val]

theorem leNat_take_one (l : List U8) (h : 1 ≤ l.length) : leNat (l.take 1) = (l.getD 0 (byte 0)).val := by
  cases l with
  | nil => simp at h
  | cons a t => simp [leNat]

/-! ## Serializers -/

theorem lenenc_ser (self : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple self buf ⦃ buf' =>
        buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by rw [hs]; exact h))
  intro b hb; rw [hb, hs]

theorem eof_ser (self : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList self.1).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple self buf ⦃ buf' =>
        buf'.val = buf.val ++ cowList self.1 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; exact h))
  intro b hb; rw [hb, hs]

theorem rawint_u8_ser (x : misc.raw.int.RawInt U8 U8) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ buf' => buf'.val = buf.val ++ [x.1] ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

theorem rawint_leu16_ser (x : misc.raw.int.RawInt misc.raw.int.LeU16 U16) (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

theorem rawint_leu24_ser (x : misc.raw.int.RawInt misc.raw.int.LeU24 U32) (buf : alloc.vec.Vec U8) (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32 x buf
      ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec _ _ h

theorem vec_len (v : alloc.vec.Vec U8) : v.length = v.val.length := rfl

theorem progressRead_enc (p : Progress) (tail : List U8) (hs : p.stage < 256) (hm : p.maxStage < 256)
    (hp : p.progress < 2 ^ 24) (hi : p.info.length < 2 ^ 64) :
    progressRead (progressEnc p ++ tail) = (some p, tail) := by
  unfold progressEnc
  have l3 := length_leBytes 3 p.progress
  obtain ⟨b3, b4, b5, h3⟩ : ∃ b3 b4 b5, leBytes 3 p.progress = [b3, b4, b5] := by
    match h : leBytes 3 p.progress, l3 with
    | [b3, b4, b5], _ => exact ⟨b3, b4, b5, rfl⟩
  have hl := leNat_leBytes 3 p.progress
  rw [h3, Nat.mod_eq_of_lt (by simpa using hp)] at hl
  unfold progressRead
  simp only [h3, List.cons_append, List.nil_append, List.length_cons]
  rw [ite_eq_right (by omega)]
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.getD_cons_succ,
    List.getD_cons_zero]
  rw [checkedLenencStr_lenencStr _ _ hi]
  simp [byte_val, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm, hl]

end mysql_common.PKUtil
