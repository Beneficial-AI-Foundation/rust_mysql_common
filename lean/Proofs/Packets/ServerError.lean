import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Packets.SqlState

/-! Statements for `struct ServerError and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

private theorem parse_sqlstate_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      if 6 ≤ buf.length then
        (okPart r).map (·.state.val) = (sqlStateRead (buf.val.take 6)).1 ∧ rest.val = buf.val.drop 6
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs : (packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple : proto.MyDeserialize packets.SqlState Unit).SIZE = ok (some 6#usize) := by
    simp [packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  by_cases hl : 6 ≤ buf.length
  · simp only [hl, ite_true]
    apply io.ParseBuf.parse_of_size _ _ _ 6#usize hs hl
      (fun (o : Option packets.SqlState) => o.map (·.state.val) = (sqlStateRead (buf.val.take 6)).1)
    intro sub hsub
    apply WP.spec_mono (packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec sub)
    rintro ⟨r, rest⟩ h1
    simp only [WP.uncurry'_pair] at h1 ⊢
    have h6 : ((6#usize : Usize) : Nat) = 6 := rfl
    rw [h6] at hsub
    rw [← hsub]
    exact congrArg Prod.fst h1
  · simp only [hl, ite_false]
    exact io.ParseBuf.parse_of_size_short _ _ _ 6#usize hs (by simp only [Slice.length] at hl ⊢; simp; omega)

private theorem eof_ser (self : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList self.1).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple self buf ⦃ buf' =>
        buf'.val = buf.val ++ cowList self.1 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; exact h))
  intro b hb; rw [hb, hs]


/-- `new`: the given fields (the message converted with `into`). -/
theorem packets.ServerError.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (code : U16) (state : Option packets.SqlState) (msg : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into msg = ok c) :
    packets.ServerError.new into code state msg ⦃ e =>
      e.code.1 = code ∧ e.state = state ∧ e.message.1 = c ⦄ := by
  unfold packets.ServerError.new
  step*

/-- `error_code`: the field. -/
theorem packets.ServerError.error_code_eq (self : packets.ServerError) :
    packets.ServerError.error_code self = ok self.code.1 := by
  rfl

/-- `sql_state_ref`: the field. -/
theorem packets.ServerError.sql_state_ref_eq (self : packets.ServerError) :
    packets.ServerError.sql_state_ref self = ok self.state := by
  unfold packets.ServerError.sql_state_ref
  cases h : self.state <;> simp

/-- `message_ref`: the message bytes. -/
theorem packets.ServerError.message_ref_spec (self : packets.ServerError) :
    packets.ServerError.message_ref self ⦃ s => s.val = cowList self.message.1 ⦄ := by
  unfold packets.ServerError.message_ref
  exact eof_as_bytes_spec _

/-- `into_owned`: the same fields. -/
theorem packets.ServerError.into_owned_spec (self : packets.ServerError) :
    packets.ServerError.into_owned self ⦃ e => ErrPkt.ofServerError e = ErrPkt.ofServerError self ⦄ := by
  unfold packets.ServerError.into_owned
  step*
  simp_all [ErrPkt.ofServerError]

/-- `MyDeserialize for ServerError`: `SIZE` is `None`. -/
theorem packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE_eq :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE = none := by
  simp [packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE]

/-- `MyDeserialize for ServerError` with context `(code, protocol_41)`: total; `serverErrorRead`. -/
@[step]
theorem packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize_spec (code : U16) (p41 : Bool) (buf : io.ParseBuf) :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize (code, p41) buf ⦃ r rest =>
      ((okPart r).map ErrPkt.ofServerError, rest.val) = serverErrorRead code.val p41 buf.val ⦄ := by
  unfold packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize serverErrorRead
  cases p41
  · simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
    step with rawint_new_spec as ⟨ri, hri⟩
    step with parse_eof_bytes_spec as ⟨r, buf1, h1, h2⟩
    cases r with
    | Err e => simp at h1
    | Ok rb =>
      simp at h1
      simp [CoreOpsTry.branch, ErrPkt.ofServerError, hri, h1, h2]
  · simp only [uncurry_apply_pair, ↓reduceIte]
    step with rawint_new_spec as ⟨ri, hri⟩
    step with parse_sqlstate_spec as ⟨r, buf1, h1⟩
    split_ifs at h1 with hl
    · obtain ⟨h1a, h1b⟩ := h1
      have hl' : (↑buf : List U8).length ≥ 6 := hl
      rw [if_neg (by omega)]
      obtain ⟨m, t, hmt⟩ : ∃ m t, (↑buf : List U8) = m :: t := by
        cases h : (↑buf : List U8) with
        | nil => simp [h] at hl'
        | cons m t => exact ⟨m, t, rfl⟩
      have ht : (List.take 5 t).length = 5 := by simp [hmt] at hl'; simp; omega
      rw [hmt] at h1a h1b ⊢
      simp only [List.take_succ_cons, sqlStateRead, ht, lt_self_iff_false, ite_false] at h1a
      simp only [List.getD_cons_zero]
      cases r with
      | Err e =>
        simp only [okPart_Err, Option.map_none] at h1a
        have hm : m.val ≠ 0x23 := by
          intro hm; rw [if_neg (by simp [hm])] at h1a; simp at h1a
        rw [if_pos hm, ← h1b]
        simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok st =>
        simp only [okPart_Ok, Option.map_some] at h1a
        have hm : m.val = 0x23 := by
          by_contra hm; rw [if_pos hm] at h1a; simp at h1a
        simp only [hm, ne_eq, not_true_eq_false, ite_false, Nat.reduceEqDiff] at h1a ⊢
        simp only [Option.some.injEq] at h1a
        simp only [CoreOpsTry.branch, bind_tc_ok]
        step with parse_eof_bytes_spec as ⟨r1, buf2, h2, h3⟩
        cases r1 with
        | Err e => simp at h2
        | Ok rb =>
          simp at h2
          simp [CoreOpsTry.branch, ErrPkt.ofServerError, hri, h2, h3, h1a, h1b]
    · obtain ⟨h1a, rfl⟩ := h1
      rw [if_pos (by simp only [Slice.length] at hl; omega)]
      cases r with
      | Ok _ => simp at h1a
      | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- `MySerialize for ServerError`: appends the SQL state (`#` and 5 bytes) if present, then the message (the code is written by `ErrPacket`). -/
@[step]
theorem packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ServerError) (buf : alloc.vec.Vec U8)
    (h : buf.length + 6 + (cowList self.message.1).length ≤ Usize.max) :
    packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (match self.state with | some s => byte 0x23 :: s.state.val | none => [])
        ++ cowList self.message.1 ⦄ := by
  unfold packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize
  cases hs : self.state with
  | none =>
    simp only
    apply WP.spec_mono (eof_ser _ _ (by omega))
    intro b hb; simp [hb]
  | some st =>
    simp only
    step with packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
    apply WP.spec_mono (eof_ser _ _ (by
      have : buf1.length = buf.length + 6 := by
        simp [alloc.vec.Vec.length, h1]
      omega))
    intro b hb; simp [hb, h1]

end mysql_common
