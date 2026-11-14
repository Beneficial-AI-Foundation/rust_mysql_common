import Defs
import Proofs.Io.ParseBuf
import Proofs.Util.ParseBuf
import Proofs.Util.BinlogCommon
import Proofs.Util.IntAndMisc
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Int.U8
import Proofs.Binlog.Consts.IntvarEventType
import Proofs.Binlog.Consts.IncidentType
import Proofs.Misc.Raw.Const.RawConst
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.Raw.Skip
import Proofs.Misc.Raw.Flags.RawFlags
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Binlog.Consts.GtidFlags

/-! Helper lemmas for the binlog-event proofs of group `BinlogEvGtid` (GTID, previous-GTIDs,
rotate, intvar, rand, XID, incident, rows-query and transaction-payload events). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogEvGtid

export _root_.mysql_common.BinlogCommon (leNat_leBytes_lt byte_val_self usize_saturating_add_val u32_max_le_usize
  lenencInt_length_le)

attribute [step] binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec
  io.ParseBuf.checked_skip_spec


theorem cast_u8_usize (x : U8) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem cast_u16_usize (x : U16) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem cast_u32_usize (x : U32) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem take_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).take k = leBytes k n := by
  simp [PBUtil.length_leBytes]

theorem drop_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).drop k = t := by
  simp [PBUtil.length_leBytes]

theorem leNat_leBytes_u8 (x : U8) : leNat (leBytes 1 x.val) = x.val :=
  leNat_leBytes_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u16 (x : U16) : leNat (leBytes 2 x.val) = x.val :=
  leNat_leBytes_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u32 (x : U32) : leNat (leBytes 4 x.val) = x.val :=
  leNat_leBytes_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u64 (x : U64) : leNat (leBytes 8 x.val) = x.val :=
  leNat_leBytes_lt _ _ (by have := x.hBounds; simpa using this)

theorem okPart_map_eq_some {T V : Type} {f : T → V} {r : core.result.Result T core.io.error.Error} {v : V}
    (h : (okPart r).map f = some v) : ∃ x, r = .Ok x ∧ f x = v := by
  cases r <;> simp_all [okPart]

/-! ## `RawInt<LeU64>` -/

@[step]
theorem rawint_leu64_parse_unchecked (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ x, r = .Ok x ∧ x.1.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have hd := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun (o : Option U64) (rest : io.ParseBuf) => o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8)
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)
  apply WP.spec_mono hd
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  cases r with
  | Ok x => exact ⟨x, rfl, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

theorem rawint_leu64_parse_unchecked_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () = fail .panic := by
  rw [io.ParseBuf.parse_unchecked_eq]
  show misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize _ () buf = _
  unfold misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact PBUtil.bind_fail_left (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics buf h)

@[step]
theorem rawint_leu64_serialize (x : misc.raw.int.RawInt misc.raw.int.LeU64 U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ buf h

theorem okPart_map_some_iff {T V : Type} (f : T → V) (r : core.result.Result T core.io.error.Error) (v : V) :
    (okPart r).map f = some v ↔ ∃ x, r = .Ok x ∧ f x = v := by
  cases r <;> simp [okPart]

theorem okPart_none_iff {T : Type} (r : core.result.Result T core.io.error.Error) :
    okPart r = none ↔ ∃ e, r = .Err e := by
  cases r <;> simp [okPart]

/-- `parse::<RawInt<LeU64>>`, in a form for `step`. -/
@[step]
theorem parse_leu64 (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then ∃ x, r = .Ok x ∧ x.1.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8
      else ∃ e, r = .Err e ⦄ := by
  apply WP.spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf)
  rintro ⟨r, rest⟩ h
  split_ifs at h ⊢
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨x, rfl, hx⟩ := (okPart_map_some_iff _ _ _).1 h1
    exact ⟨x, rfl, hx, h2⟩
  · exact (okPart_none_iff _).1 h.1

/-- `parse::<RawBytes<EofBytes>>`: the rest of the buffer. -/
@[step]
theorem parse_eof_bytes (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ∃ x, r = .Ok x ∧ cowList x.1 = buf.val ∧ rest.val = [] ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ buf () (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  have hd := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf
    (fun o rest => o = some buf.val ∧ rest.val = [])
    (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  apply WP.spec_mono hd
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  obtain ⟨x, rfl, hx⟩ := (okPart_map_some_iff _ _ _).1 h1
  exact ⟨x, rfl, hx, h2⟩

@[step]
theorem lift_usize_saturating_add (x y : Usize) :
    lift (core.num.Usize.saturating_add x y) ⦃ r => r.val = min (x.val + y.val) Usize.max ⦄ := by
  simp [lift, usize_saturating_add_val]

@[step]
theorem lift_cast_u32_max :
    lift (UScalar.cast .Usize core.num.U32.MAX) ⦃ r => r.val = 2 ^ 32 - 1 ⦄ := by
  simp only [lift, WP.spec_ok]
  rw [cast_u32_usize]; simp [core.num.U32.MAX, U32.rMax]

theorem header_len_val : binlog.events.BinlogEventHeader.LEN.val = 19 := by
  simp [binlog.events.BinlogEventHeader.LEN]

/-- `RawBytes<EofBytes>::serialize`: appends the bytes. -/
@[step]
theorem rawbytes_eof_serialize (x : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList x.1).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple x buf ⦃ buf' => buf'.val = buf.val ++ cowList x.1 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; exact h))
  intro b hb; rw [hb, hs]

/-! ## `Const<IntvarEventType, u8>` -/

@[step]
theorem const_new_spec {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t ⦃ c => c.1 = t ⦄ := by
  have e : misc.raw._const.Const.new U t = ok (t, ()) := rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

theorem list_cons_of_length_pos {α : Type} (l : List α) (h : 1 ≤ l.length) : ∃ b t, l = b :: t := by
  cases l with
  | nil => simp at h
  | cons b t => exact ⟨b, t, rfl⟩

theorem rawint_parse_unchecked_fail {T P : Type} (inst : misc.raw.int.IntRepr T P) (buf : io.ParseBuf) (e : Error)
    (h : inst.deserialize buf = fail e) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () = fail e := by
  rw [io.ParseBuf.parse_unchecked_eq]
  show misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize _ () buf = _
  unfold misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact PBUtil.bind_fail_left h

theorem parse_unchecked_intvar_type_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType
      binlog.consts.UnknownIntvarEventType.Insts.CoreErrorError) buf () = fail .panic := by
  rw [io.ParseBuf.parse_unchecked_eq]
  show misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize _ _ _ () buf = _
  unfold misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact PBUtil.bind_fail_left (rawint_parse_unchecked_fail _ buf _
    (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_panics buf h))

@[step]
theorem parse_unchecked_intvar_type (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType
      binlog.consts.UnknownIntvarEventType.Insts.CoreErrorError) buf () ⦃ r rest =>
      rest.val = buf.val.drop 1 ∧
      ∀ b, buf.val.head? = some b → (match intvarTypeOfCode b.val with
        | some t => ∃ x, r = .Ok x ∧ x.1 = t
        | none => ∃ e, r = .Err e) ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have hd := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    U8.Insts.Mysql_commonMiscRawIntIntReprU8
    binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType
    binlog.consts.UnknownIntvarEventType.Insts.CoreErrorError buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1)
    (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h)
    (fun p o => o = intvarTypeOfCode p.val)
    (by
      intro p
      show binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from p ⦃ r =>
        okPart r = intvarTypeOfCode p.val ⦄
      rw [binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from_spec]
      simp only [WP.spec_ok]
      cases intvarTypeOfCode p.val <;> rfl)
  apply WP.spec_mono hd
  rintro ⟨r, rest⟩ ⟨o, ⟨ho, hrest⟩, hm⟩
  refine ⟨hrest, ?_⟩
  intro b hb
  obtain ⟨b0, l, hl⟩ : ∃ b0 l, buf.val = b0 :: l := by
    cases hc : buf.val with
    | nil => simp [hc] at hb
    | cons b0 l => exact ⟨b0, l, rfl⟩
  rw [hl] at hb ho
  simp only [List.head?_cons, Option.some.injEq] at hb
  subst hb
  cases o with
  | none => simp at ho
  | some p =>
  simp only [Option.map_some, Option.some.injEq, List.take_succ_cons, List.take_zero, leNat] at ho
  have hp' : p.val = b0.val := by simpa using ho
  simp only at hm
  rw [hp'] at hm
  cases ht : intvarTypeOfCode b0.val with
  | some t =>
    rw [ht] at hm
    obtain ⟨x, rfl, hx⟩ := (okPart_map_some_iff _ _ _).1 hm
    exact ⟨x, rfl, hx⟩
  | none =>
    rw [ht] at hm
    simp only
    cases r with
    | Ok x => simp [okPart] at hm
    | Err e => exact ⟨e, rfl⟩

@[step]
theorem rawint_u8_serialize (x : misc.raw.int.RawInt U8 U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf ⦃ buf' => buf'.val = buf.val ++ [x.1] ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ buf h

@[step]
theorem const_intvar_serialize (c : misc.raw._const.Const binlog.consts.IntvarEventType U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
      binlog.consts.IntvarEventType.Insts.CoreMarkerCopy (core.convert.IntoFrom
      U8.Insts.CoreConvertFromIntvarEventType)
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 c buf ⦃ buf' => buf'.val = buf.val ++ [byte (intvarTypeCode c.1)] ⦄ := by
  obtain ⟨t, u⟩ := c
  unfold misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [core.convert.IntoFrom.into]
  step with U8.Insts.CoreConvertFromIntvarEventType.from_spec as ⟨p, hp⟩
  step*
  have hbp : byte (intvarTypeCode t) = p := by rw [← hp, byte_val_self]
  rw [hbp]
  simp_all

/-! ## `ReadsAs` -/

theorem readsAs_of {T V : Type} (view : T → V) (spec : Option (V × List U8))
    (r : core.result.Result T core.io.error.Error) (rest : io.ParseBuf)
    (h1 : (okPart r).map view = spec.map Prod.fst) (h2 : ∀ v t, spec = some (v, t) → rest.val = t) :
    ReadsAs view spec r rest := by
  unfold ReadsAs
  match spec, h1, h2 with
  | some (v, t), h1, h2 => exact ⟨h1, h2 v t rfl⟩
  | none, h1, _ => simpa using h1

theorem readsAs_fst {T V : Type} (view : T → V) (spec : Option (V × List U8))
    (r : core.result.Result T core.io.error.Error) (rest : io.ParseBuf) (h : ReadsAs view spec r rest) :
    (okPart r).map view = spec.map Prod.fst := by
  unfold ReadsAs at h
  match spec, h with
  | some (v, t), h => simpa using h.1
  | none, h => simp [h]

theorem intvarTypeOfCode_code (t : binlog.consts.IntvarEventType) : intvarTypeOfCode (intvarTypeCode t) = some t := by
  cases t <;> rfl

theorem intvarTypeCode_lt (t : binlog.consts.IntvarEventType) : intvarTypeCode t < 3 := by
  cases t <;> simp [intvarTypeCode]

/-! ## `RawConst<LeU16, IncidentType>`, `RawBytes<U8Bytes>` -/

@[step]
theorem parse_rawconst_leu16 (U : Type) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then ∃ x, r = .Ok x ∧ x.1.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2
      else ∃ e, r = .Err e ⦄ := by
  have hs : proto.MyDeserialize.SIZE (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) = ok (some 2#usize) := by
    simp [misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq,
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq]
  by_cases hl : 2 ≤ buf.length
  · have := io.ParseBuf.parse_of_size _ buf () 2#usize hs hl
      (fun o => o.map (fun x => x.1.val) = some (leNat (buf.val.take 2)))
    apply WP.spec_mono (this ?_)
    · rintro ⟨r, rest⟩ ⟨h1, h2⟩
      simp only [hl, ite_true]
      obtain ⟨x, rfl, hx⟩ := (okPart_map_some_iff _ _ _).1 h1
      exact ⟨x, rfl, hx, h2⟩
    · intro sub hsub
      have hsl : 2 ≤ sub.length := by simp [Slice.length, hsub]; scalar_tac
      have hd := misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec U
        misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 sub
        (fun (o : Option U16) (rest : io.ParseBuf) => o.map (·.val) = some (leNat (sub.val.take 2)) ∧ rest.val = sub.val.drop 2)
        (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec sub hsl)
      apply WP.spec_mono hd
      rintro ⟨r, rest⟩ ⟨h1, -⟩
      simp only [WP.uncurry']
      have h1' : Option.map (fun x => x.1.val) (okPart r) = some (leNat (List.take 2 sub.val)) := by
        rw [← h1, Option.map_map]; rfl
      rw [h1', hsub]; simp [List.take_take]
  · simp only [hl, ite_false]
    apply WP.spec_mono (io.ParseBuf.parse_of_size_short _ buf () 2#usize hs (by scalar_tac))
    rintro ⟨r, rest⟩ ⟨h1, -⟩
    exact (okPart_none_iff _).1 h1

@[step]
theorem parse_u8bytes (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ buf () (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf
    (fun o rest => (o, rest.val) = checkedLenPrefixed 1 buf.val)
    (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

@[step]
theorem rawconst_leu16_serialize {U : Type} (x : misc.raw._const.RawConst misc.raw.int.LeU16 U U16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ buf h

@[step]
theorem rawbytes_u8_serialize (x : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + min (cowList x.1).length 255 ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple x buf ⦃ buf' => buf'.val = buf.val ++ u8Str (cowList x.1) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; exact h))
  intro b hb; rw [hb, u8Str, ← hs]

theorem incidentRead_eq (bs : List U8) (h : 2 ≤ bs.length) (o : Option (List U8)) (rr : List U8)
    (hc : checkedLenPrefixed 1 (bs.drop 2) = (o, rr)) :
    incidentRead bs = o.map (fun m => ((leNat (bs.take 2), m), rr)) := by
  cases o <;> simp [incidentRead, takeExact, h, hc, optFst]

theorem checkedLenPrefixed_u8Str (s tail : List U8) (hs : s.length ≤ 255) :
    checkedLenPrefixed 1 (u8Str s ++ tail) = (some s, tail) := by
  have hb : (byte s.length).val = s.length := by
    show (BitVec.ofNat 8 s.length).toNat = s.length
    simp; omega
  have h1 : min s.length 255 = s.length := by omega
  simp [u8Str, h1, List.take_of_length_le hs, checkedLenPrefixed, readLE, leNat, hb]

/-! ## `Skip<LEN>` -/

@[step]
theorem parse_skip (LEN : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple LEN) buf () ⦃ r rest =>
      if LEN.val ≤ buf.length then (∃ x, r = .Ok x) ∧ rest.val = buf.val.drop LEN.val
      else ∃ e, r = .Err e ⦄ := by
  have hs : proto.MyDeserialize.SIZE (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple LEN) = ok (some LEN) := by
    simp [misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  by_cases hl : LEN.val ≤ buf.length
  · have := io.ParseBuf.parse_of_size _ buf () LEN hs hl (fun o => o.isSome)
    apply WP.spec_mono (this ?_)
    · rintro ⟨r, rest⟩ ⟨h1, h2⟩
      simp only [hl, ite_true]
      refine ⟨?_, h2⟩
      cases r with
      | Ok x => exact ⟨x, rfl⟩
      | Err e => simp [okPart] at h1
    · intro sub hsub
      have hsl : LEN.val ≤ sub.length := by simp [Slice.length, hsub]; omega
      apply WP.spec_mono (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec LEN sub hsl)
      rintro ⟨r, rest⟩ ⟨h1, -⟩
      exact h1
  · simp only [hl, ite_false]
    apply WP.spec_mono (io.ParseBuf.parse_of_size_short _ buf () LEN hs (by omega))
    rintro ⟨r, rest⟩ ⟨h1, -⟩
    exact (okPart_none_iff _).1 h1

attribute [step] misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec

/-- The usual `len` cap: saturating at `usize::MAX` below the `u32::MAX - 19` cap changes nothing. -/
theorem min_usize_cap (a : Nat) : min (min a Usize.max) (2 ^ 32 - 1 - 19) = min a (2 ^ 32 - 1 - 19) := by
  have hM := u32_max_le_usize
  have hC : 2 ^ 32 - 1 - 19 ≤ Usize.max := Nat.le_trans (by norm_num) hM
  rw [min_assoc, min_eq_right hC]

theorem min_one_usize : min (0 + 1) Usize.max = 1 := by
  have hM := u32_max_le_usize
  exact min_eq_left (Nat.le_trans (by norm_num) hM)

/-! ## Defaults -/

@[step]
theorem rawint_default_u64 {T : Type} (d : core.default.Default T) (inst : misc.raw.int.IntRepr T U64) :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default d inst core.default.DefaultU64 ⦃ r => r.1.val = 0 ⦄ := by
  simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem rawint_default_u32 {T : Type} (d : core.default.Default T) (inst : misc.raw.int.IntRepr T U32) :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default d inst core.default.DefaultU32 ⦃ r => r.1.val = 0 ⦄ := by
  simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem rawflags_default_u8 {T U : Type} (d : core.default.Default T) (fl : bitflags.traits.Flags T U8) (du : core.default.Default U) :
    misc.raw.flags.RawFlags.Insts.CoreDefaultDefault.default d fl du core.default.DefaultU8 ⦃ r => r.1.val = 0 ⦄ := by
  simp [misc.raw.flags.RawFlags.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  exact (WP.spec_ok _).mpr rfl

/-! ## Length-encoded integers -/

theorem cast_u8_u64 (x : U8) : (UScalar.cast .U64 x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem lenencInt_length_pos (n : Nat) : 1 ≤ (lenencInt n).length := by
  unfold lenencInt; split_ifs <;> simp [PBUtil.length_leBytes]

theorem lenencInt_small_length (n : Nat) (h : n < 251) : (lenencInt n).length = 1 := by
  simp [lenencInt, h]

theorem lenencInt_lenlen_length (n : Nat) : (lenencInt (lenencInt n).length).length = 1 :=
  lenencInt_small_length _ (by have := lenencInt_length_le n; omega)

/-! ## Vectors and byte arrays -/

@[step]
theorem extend_from_slice_u8 (buf : alloc.vec.Vec U8) (s : Slice U8) (h : buf.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 buf s ⦃ b' => b'.val = buf.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intro x _; rfl))
  intro l hl
  simp [hl.1]

@[step]
theorem lift_u64_to_le_bytes (x : U64) :
    lift (core.num.U64.to_le_bytes x) ⦃ y => y.val = leBytes 8 x.val ⦄ := by
  apply WP.spec_mono (core.num.U64.to_le_bytes.step_spec x)
  intro y hy; rw [hy, IntAndMisc.leBytes_bv 8 rfl]; rfl

@[step]
theorem lift_array_to_slice {α : Type} {n : Usize} (a : Std.Array α n) :
    lift (Std.Array.to_slice a) ⦃ s => s.val = a.val ⦄ := by
  simp [lift, Std.Array.to_slice]

theorem cast_usize_u64 (x : Usize) : (UScalar.cast .U64 x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
    simp only [UScalarTy.numBits]; cases System.Platform.numBits_eq <;> simp [*])

@[step]
theorem lift_cast_usize_u64 (x : Usize) :
    lift (UScalar.cast .U64 x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok]; exact cast_usize_u64 x

end mysql_common.BinlogEvGtid
