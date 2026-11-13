import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Util.IntAndMisc
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Int.U8
import Proofs.Packets.SessionStateChange.SessionStateChange

/-! Statements for `struct SessionStateInfo and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for SessionStateType`: the type of code `value` (codes 0–5). -/
private theorem ssty_try_from_eq (value : U8) :
    constants.SessionStateType.Insts.CoreConvertTryFromU8UnknownSessionStateType.try_from value =
      ok (match sessionStateTypeOfCode value.val with
        | some t => .Ok t
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

/-- `From<SessionStateType> for u8`: the type code. -/
private theorem ssty_from_spec (t : constants.SessionStateType) :
    U8.Insts.CoreConvertFromSessionStateType.from t ⦃ r => r.val = sessionStateTypeCode t ⦄ := by
  cases t <;> simp [U8.Insts.CoreConvertFromSessionStateType.from, sessionStateTypeCode,
    read_discriminant, constants.SessionStateType.read_discriminant]

private theorem ssty_serialize (x : misc.raw._const.Const constants.SessionStateType U8)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
      constants.SessionStateType.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromSessionStateType)
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ b => b.val = buf.val ++ [byte (sessionStateTypeCode x.1)] ⦄ := by
  obtain ⟨p, hp, hpv⟩ := mysql_common.PBUtil.spec_eq_ok (ssty_from_spec x.1)
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ p hp, ← hpv,
    PCSUtil.byte_eq_self]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

/-- `into_owned`: the same type and data. -/
theorem packets.SessionStateInfo.into_owned_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.into_owned self ⦃ s => SsInfo.of s = SsInfo.of self ⦄ := by
  unfold packets.SessionStateInfo.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb, hrb ⟩
  simp [SsInfo.of, hrb]

/-- `data_type`: the type. -/
theorem packets.SessionStateInfo.impl.data_type_eq (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.impl.data_type self = ok self.data_type.1 := by
  unfold packets.SessionStateInfo.impl.data_type
  exact misc.raw._const.Const.deref_eq _

/-- `data_ref`: the raw data. -/
theorem packets.SessionStateInfo.data_ref_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.data_ref self ⦃ s => s.val = cowList self.data.1 ⦄ := by
  unfold packets.SessionStateInfo.data_ref
  exact PCSUtil.lenenc_as_bytes _

/-- `decode`: total; the data read as a change of the entry's type (`ssChangeRead`). Bytes of
    the data after the change are ignored. -/
theorem packets.SessionStateInfo.decode_spec (h64 : Target64) (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.decode self ⦃ r =>
      (okPart r).map SsChange.of = (ssChangeRead self.data_type.1 (cowList self.data.1)).1 ⦄ := by
  unfold packets.SessionStateInfo.decode
  step with PCSUtil.lenenc_as_bytes as ⟨ s, hs ⟩
  rw [misc.raw._const.Const.deref_eq, bind_ok, io.ParseBuf.parse_unchecked_eq]
  step with packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec h64 as ⟨ r, rest, hr ⟩
  rw [← hs, ← hr]

/-- `MyDeserialize for SessionStateInfo`: `SIZE` is `None`. -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- The type byte, read by `Const<SessionStateType, u8>` from a non-empty buffer. -/
private theorem d_ssty (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      constants.SessionStateType.Insts.CoreConvertTryFromU8UnknownSessionStateType
      constants.UnknownSessionStateType.Insts.CoreErrorError () buf ⦃ r rest =>
      (okPart r).map (·.1) = sessionStateTypeOfCode x.val ∧ rest.val = t ⦄ := by
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    U8.Insts.Mysql_commonMiscRawIntIntReprU8
    constants.SessionStateType.Insts.CoreConvertTryFromU8UnknownSessionStateType
    constants.UnknownSessionStateType.Insts.CoreErrorError buf
    (fun (o : Option U8) (rest : io.ParseBuf) => o = some x ∧ rest.val = t)
    (by
      apply WP.spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp only [WP.uncurry', hb, List.take, List.drop, leNat] at h ⊢
      refine ⟨?_, h.2⟩
      cases r <;> simp_all [okPart]
      rename_i a
      rw [← PCSUtil.byte_eq_self a, ← PCSUtil.byte_eq_self x, h.1])
    (fun (p : U8) (o : Option constants.SessionStateType) => o = sessionStateTypeOfCode p.val)
    (by
      intro p
      simp only [ssty_try_from_eq]
      apply (WP.spec_ok _).mpr
      cases sessionStateTypeOfCode p.val <;> rfl)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨rfl, h2⟩, h3⟩
  exact ⟨h3, h2⟩

/-- The type byte, read by `parse` (checked through `SIZE`). -/
private theorem parse_ssty (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      constants.SessionStateType.Insts.CoreConvertTryFromU8UnknownSessionStateType
      constants.UnknownSessionStateType.Insts.CoreErrorError) buf () ⦃ r rest =>
      match buf.val with
      | [] => okPart r = none ∧ rest.val = []
      | x :: t => (okPart r).map (·.1) = sessionStateTypeOfCode x.val ∧ rest.val = t ⦄ := by
  have := IntAndMisc.parse_fixed (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      constants.SessionStateType.Insts.CoreConvertTryFromU8UnknownSessionStateType
      constants.UnknownSessionStateType.Insts.CoreErrorError) 1#usize
    (by simp [misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq,
      U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq]) buf ()
    (fun o => o.map (·.1) = sessionStateTypeOfCode (buf.val.headD 0#u8).val) (by
      intro sub hsub hl
      obtain ⟨x, t, hb⟩ : ∃ x t, buf.val = x :: t := by
        match h : buf.val with
        | [] => simp [Slice.length, h] at hl
        | x :: t => exact ⟨x, t, rfl⟩
      rw [hb] at hsub
      apply WP.spec_mono (d_ssty sub x [] (by simpa using hsub))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hb] using h1)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'] at h ⊢
  split_ifs at h with hl
  · obtain ⟨h1, h2⟩ := h
    match hb : buf.val with
    | [] => simp [Slice.length, hb] at hl
    | x :: t => simp only [hb] at h1 h2; exact ⟨by simpa using h1, by simpa using h2⟩
  · obtain ⟨h1, h2⟩ := h
    match hb : buf.val with
    | [] => exact ⟨h1, by rw [h2, hb]⟩
    | x :: t => simp [Slice.length, hb] at hl

/-- `MyDeserialize for SessionStateInfo`: total; `ssInfoRead` (a type code 0–5, then the data as
    a length-encoded string). -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map SsInfo.of, rest.val) = ssInfoRead buf.val ⦄ := by
  unfold packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with parse_ssty buf as ⟨ r, buf1, h1 ⟩
  cases hb : buf.val with
  | nil =>
    simp only [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Ok v => simp [okPart] at hr
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart,
        ssInfoRead, hb1]
  | cons x t =>
    simp only [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Ok v =>
      simp only [okPart, Option.map_some] at hr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with PKUtil.parse_lenenc_bytes_spec h64 buf1 as ⟨ r2, buf2, h2 ⟩
      rw [hb1] at h2
      simp only [ssInfoRead, ← hr, ← h2]
      cases r2 with
      | Ok rb => simp [okPart, SsInfo.of]
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
    | Err e =>
      simp only [okPart, Option.map_none] at hr
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart,
        ssInfoRead, ← hr, hb1]

/-- Round trip: an entry in the protocol layout (`ssInfoEnc`) is read back. -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (s : packets.SessionStateInfo) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = ssInfoEnc (SsInfo.of s) ++ tail) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SsInfo.of = some (SsInfo.of s) ∧ rest.val = tail ⦄ := by
  have hmax : Usize.max < 2 ^ 64 := by
    rw [Usize.max_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all
  have hl : (cowList s.data.1).length < 2 ^ 64 :=
    lt_of_le_of_lt (PCSUtil.cowList_length_le _) hmax
  have hty : sessionStateTypeOfCode (byte (sessionStateTypeCode s.data_type.1)).val =
      some s.data_type.1 := by
    cases s.data_type.1 <;> rfl
  apply WP.spec_mono (packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'] at hr ⊢
  rw [h] at hr
  simp only [ssInfoEnc, SsInfo.of, List.cons_append, ssInfoRead, hty,
    PKUtil.checkedLenencStr_lenencStr _ _ hl, Prod.mk.injEq] at hr
  exact ⟨by rw [hr.1]; rfl, hr.2⟩

/-- `MySerialize for SessionStateInfo`: appends `ssInfoEnc` (the type code, then the data as a
    length-encoded string). -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SessionStateInfo) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssInfoEnc (SsInfo.of self)).length ≤ Usize.max) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssInfoEnc (SsInfo.of self) ⦄ := by
  unfold packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [ssInfoEnc, SsInfo.of, List.length_cons] at h
  step with ssty_serialize as ⟨ b1, h1 ⟩
  step with PCSUtil.lenenc_raw_serialize as ⟨ b2, h2 ⟩
  · simp only [PKUtil.vec_len, h1] at *; simp; omega
  simp [h2, h1, ssInfoEnc, SsInfo.of]

end mysql_common
