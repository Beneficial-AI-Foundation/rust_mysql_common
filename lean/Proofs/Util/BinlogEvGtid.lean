import Defs
import Proofs.Io.ParseBuf
import Proofs.Util.ParseBuf
import Proofs.Util.IntAndMisc
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.RawBytes

/-! Helper lemmas for the binlog-event proofs of group `BinlogEvGtid` (GTID, previous-GTIDs,
rotate, intvar, rand, XID, incident, rows-query and transaction-payload events). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogEvGtid


@[step]
theorem get_event_type_header_length_step (e : binlog.events.format_description_event.FormatDescriptionEvent) (t : binlog.consts.EventType) :
    binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length e t ⦃ n => n.val = postHeaderLen (fdeLens e) t ⦄ :=
  binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec e t

@[step]
theorem checked_skip_step (buf : io.ParseBuf) (cnt : Usize) :
    io.ParseBuf.checked_skip buf cnt ⦃ b rest =>
      if cnt.val ≤ buf.length then b = true ∧ rest.val = buf.val.drop cnt.val
      else b = false ∧ rest = buf ⦄ :=
  io.ParseBuf.checked_skip_spec buf cnt

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

theorem leNat_leBytes_of_lt (k n : Nat) (h : n < 2 ^ (8 * k)) : leNat (leBytes k n) = n := by
  rw [PBUtil.leNat_leBytes, Nat.mod_eq_of_lt h]

theorem leNat_leBytes_u8 (x : U8) : leNat (leBytes 1 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u16 (x : U16) : leNat (leBytes 2 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u32 (x : U32) : leNat (leBytes 4 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u64 (x : U64) : leNat (leBytes 8 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)

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

theorem usize_saturating_add_val (x y : Usize) :
    (core.num.Usize.saturating_add x y).val = min (x.val + y.val) Usize.max := by
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.max_USize_eq]
  rw [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · omega
  · have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      rw [Usize.max_def]; simp [Usize.numBits]
    omega

@[step]
theorem lift_usize_saturating_add (x y : Usize) :
    lift (core.num.Usize.saturating_add x y) ⦃ r => r.val = min (x.val + y.val) Usize.max ⦄ := by
  simp [lift, usize_saturating_add_val]

theorem u32_max_le_usize : 2 ^ 32 - 1 ≤ Usize.max := by
  rw [Usize.max_def]; simp only [Usize.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

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

end mysql_common.BinlogEvGtid
