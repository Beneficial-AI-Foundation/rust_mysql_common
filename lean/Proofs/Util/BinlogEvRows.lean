import Defs
import Proofs.Util.ParseBuf
import Proofs.Util.IntAndMisc
import Proofs.Util.RawBytesSeq
import Proofs.Util.PacketsColStmt
import Proofs.Util.PacketsOkErr
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU48
import Proofs.Misc.Raw.Int.LenEnc
import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Misc.Raw.Flags.RawFlags
import Proofs.Misc.Raw.Skip
import Proofs.Misc.Raw.Seq.RawSeq
import Proofs.Misc.Raw.Const.RawConst
import Proofs.Misc.LenencIntLen
import Proofs.Misc.LenencStrLen
import Proofs.Constants.ColumnType
import Proofs.Binlog.Consts.RowsEventFlags
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Defs.LemmasBinlogEvents

/-! Helper lemmas for the table-map and rows events (`Proofs/Binlog/Events/{TableMapEvent,RowsEvent,*RowsEvent*}`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BERUtil

theorem eof_as_bytes (rb : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = cowList rb.1 ⦄ := PKUtil.eof_as_bytes_spec rb

/-- `RowsEventFlags::from_bits_truncate` (through the `Flags` instance): the known bits. -/
theorem rows_flags_truncate (b : U16) :
    binlog.consts.RowsEventFlags.Insts.BitflagsTraitsFlagsU16.from_bits_truncate b ⦃ f => f.val = b.val &&& rowsEventFlagsAll ⦄ := by
  simp [binlog.consts.RowsEventFlags.Insts.BitflagsTraitsFlagsU16.FLAGS, bitflags.traits.Flag.new,
    U16.Insts.BitflagsTraitsBits.EMPTY,
    binlog.consts.RowsEventFlags.Insts.BitflagsTraitsFlagsU16.bits,
    binlog.consts.RowsEventFlags.Insts.BitflagsTraitsFlagsU16.from_bits_retain,
    binlog.consts.RowsEventFlags.from_bits_retain, binlog.consts.RowsEventFlags.bits,
    binlog.consts.RowsEventFlags.STMT_END, binlog.consts.RowsEventFlags.NO_FOREIGN_KEY_CHECKS,
    binlog.consts.RowsEventFlags.RELAXED_UNIQUE_CHECKS, binlog.consts.RowsEventFlags.COMPLETE_ROWS,
    Array.to_slice, Array.make, List.foldlM, U16.Insts.CoreOpsBitBitOrU16U16.bitor,
    U16.Insts.CoreOpsBitBitAndU16U16.bitand]
  simp [rowsEventFlagsAll]

/-! ## Event types -/

theorem disc_val (a : binlog.consts.EventType) : (read_discriminant a).val = eventTypeCode a := by
  cases a <;> rfl

theorem ev_eq (a b : binlog.consts.EventType) :
    binlog.consts.EventType.Insts.CoreCmpPartialEqEventType.eq a b = ok (decide (eventTypeCode a = eventTypeCode b)) := by
  simp only [binlog.consts.EventType.Insts.CoreCmpPartialEqEventType.eq, ← disc_val]
  congr 2
  apply propext; constructor
  · intro h; simp only [read_discriminant] at *; rw [h]
  · intro h; exact UScalar.eq_of_val_eq h

/-! ## Arithmetic -/

@[step] theorem usize_sat_add (x y : Usize) :
    lift (core.num.Usize.saturating_add x y) ⦃ z => z.val = min (x.val + y.val) Usize.max ⦄ := by
  simp only [lift, WP.spec_ok, core.num.Usize.saturating_add, UScalar.saturating_add]
  have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    have h1 := Usize.max_def; rw [Usize.numBits_def] at h1
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  simp only [UScalar.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := min_le_left (UScalar.max UScalarTy.Usize) (x.bv.toNat + y.bv.toNat); simp [UScalar.max] at *)]
  simp [UScalar.max, Usize.max, Nat.min_comm, Usize.numBits_def]

theorem usize_max_ge_cap : 2 ^ 32 - 1 ≤ Usize.max := by
  have h1 := Usize.max_def; rw [Usize.numBits_def] at h1
  rcases System.Platform.numBits_eq with h | h <;> simp [h] at h1 <;> omega

theorem bitmap_max_len (h64 : Target64) :
    misc.raw.bytes.BareBitmapBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN ⦃ m => m.val = 2 ^ 61 ⦄ := by
  unfold misc.raw.bytes.BareBitmapBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN
  have hn : UScalarTy.Usize.numBits = 64 := by simp [Target64] at h64; simp [UScalarTy.numBits, h64]
  step*

/-! ## Serialization -/

@[step] theorem leu48_ser (x : misc.raw.int.RawInt misc.raw.int.LeU48 U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 6 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64 x buf ⦃ b => b.val = buf.val ++ leBytes 6 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ _ h

@[step] theorem rows_flags_ser (x : misc.raw.flags.RawFlags binlog.consts.RowsEventFlags misc.raw.int.LeU16 U16)
    (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize
      binlog.consts.RowsEventFlags.Insts.BitflagsTraitsFlagsU16
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

@[step] theorem lenenc_rawint_ser (x : misc.raw.int.RawInt misc.raw.int.LenEnc U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt x.1.val).length ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64 x buf ⦃ b => b.val = buf.val ++ lenencInt x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ _ h

@[step] theorem eof_ser (rb : misc.raw.bytes.RawBytes misc.raw.bytes.EofBytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList rb.1).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf ⦃ b => b.val = buf.val ++ cowList rb.1 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  rw [← hs]
  exact misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf (by simp [Slice.length, hs, h])

theorem bitmap_ser (h64 : Target64) (rb : misc.raw.bytes.RawBytes misc.raw.bytes.BareBitmapBytes Usize) (buf : alloc.vec.Vec U8)
    (h : buf.length + min (cowList rb.1).length (2 ^ 61) ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.BareBitmapBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize rb buf ⦃ b => b.val = buf.val ++ (cowList rb.1).take (2 ^ 61) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  simp only [misc.raw.bytes.BareBitmapBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize]
  step with bitmap_max_len h64 as ⟨ m, hm ⟩
  step*
  rw [b_post, s_post, len_post, hm, ← hs]
  simp [List.slice, Slice.len]
  exact Nat.min_comm _ _

theorem extra_core (ex : misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 65533#usize) Usize) (buf : alloc.vec.Vec U8)
    (h : buf.length + (2 + min (cowList ex.1).length 65533) ≤ Usize.max) :
    (do
      let i ← misc.raw.bytes.RawBytes.len (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65533#usize) ex
      let i1 ← lift (core.num.Usize.saturating_add i 2#usize)
      let i2 ← lift (UScalar.cast UScalarTy.Usize core.num.U16.MAX)
      let i3 ← core.cmp.min core.cmp.OrdUsize i1 i2
      let len ← lift (UScalar.cast UScalarTy.U16 i3)
      let buf1 ← alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u16_le buf len
      misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
        (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65533#usize) ex buf1) ⦃ b =>
      b.val = buf.val ++ (leBytes 2 (min (cowList ex.1).length 65533 + 2) ++ (cowList ex.1).take 65533) ⦄ := by
  have hm : (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65533#usize).MAX_LEN = ok 65533#usize := by
    show ok (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN 65533#usize) = _
    rw [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]
  step with misc.raw.bytes.RawBytes.len_spec _ 65533#usize hm as ⟨ i, hi ⟩
  step*
  have hcap := usize_max_ge_cap
  have hi2 : i2.val = 65535 := by
    rw [i2_post]; simp [UScalar.cast_val_eq, core.num.U16.MAX]
    rcases System.Platform.numBits_eq with h | h <;> simp [h, U16.rMax]
  have hl : len.val = min (cowList ex.1).length 65533 + 2 := by
    rw [len_post, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]
    rw [i3_post, i1_post, hi2, hi]; omega
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec _ s buf1 (by simp [Slice.length, hs, buf1_post] at *; omega))
  intro b hb
  simp [hb, buf1_post, hl, hs]

theorem extra_ser (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (if rowsIsV2 e.event_type then 2 + min (cowList e.extra_data.1).length 65533 else 0) ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.serialize_extra_data e buf ⦃ b => b.val = buf.val ++
      (if rowsIsV2 e.event_type then leBytes 2 (min (cowList e.extra_data.1).length 65533 + 2) ++ (cowList e.extra_data.1).take 65533 else []) ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.serialize_extra_data
  simp only [ev_eq, bind_ok]
  have hw : eventTypeCode .WRITE_ROWS_EVENT = 30 := rfl
  have hu : eventTypeCode .UPDATE_ROWS_EVENT = 31 := rfl
  have hd : eventTypeCode .DELETE_ROWS_EVENT = 32 := rfl
  have hp : eventTypeCode .PARTIAL_UPDATE_ROWS_EVENT = 39 := rfl
  simp only [hw, hu, hd, hp]
  by_cases c1 : eventTypeCode e.event_type = 30
  · have hv : rowsIsV2 e.event_type = true := by simp [rowsIsV2, c1]
    simp only [c1, decide_true, ite_true, hv] at h ⊢; exact extra_core _ _ h
  by_cases c2 : eventTypeCode e.event_type = 31
  · have hv : rowsIsV2 e.event_type = true := by simp [rowsIsV2, c2]
    simp only [c2, decide_true, ite_true, hv] at h ⊢; exact extra_core _ _ h
  by_cases c3 : eventTypeCode e.event_type = 32
  · have hv : rowsIsV2 e.event_type = true := by simp [rowsIsV2, c3]
    simp only [c3, decide_true, ite_true, hv] at h ⊢; exact extra_core _ _ h
  by_cases c4 : eventTypeCode e.event_type = 39
  · have hv : rowsIsV2 e.event_type = true := by simp [rowsIsV2, c4]
    simp only [c4, decide_true, ite_true, hv] at h ⊢; exact extra_core _ _ h
  have hv : rowsIsV2 e.event_type = false := by simp [rowsIsV2, c1, c2, c3, c4]
  simp [c1, c2, c3, c4, hv]

theorem ser_bitmap (h64 : Target64) (o : Option (misc.raw.bytes.RawBytes misc.raw.bytes.BareBitmapBytes Usize)) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((o.map (fun b => (cowList b.1).take (2 ^ 61))).getD []).length ≤ Usize.max) :
    binlog.events.rows_event.serialize_bitmap o buf ⦃ b => b.val = buf.val ++ (o.map (fun b => (cowList b.1).take (2 ^ 61))).getD [] ⦄ := by
  unfold binlog.events.rows_event.serialize_bitmap
  cases o with
  | none => simp
  | some rb =>
    simp only
    have hb : buf.length = buf.val.length := rfl
    exact bitmap_ser h64 rb buf (by simp at h; omega)

/-- `serialize` of a rows event, on a 64-bit target. -/
theorem rows_serialize64 (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [rowsEnc, List.length_append] at h
  have hb : buf.length = buf.val.length := rfl
  have hv : (if rowsIsV2 e.event_type = true then 2 + min (cowList e.extra_data.1).length 65533 else 0) = (if rowsIsV2 e.event_type = true then
          leBytes 2 (min (cowList e.extra_data.1).length 65533 + 2) ++ List.take 65533 (cowList e.extra_data.1) else []).length := by
    split_ifs <;> simp; omega
  have h6 := length_leBytes 6 e.table_id.1.val
  have h2 := length_leBytes 2 e.flags.1.val
  step with leu48_ser as ⟨ b1, hb1 ⟩
  step with rows_flags_ser as ⟨ b2, hb2 ⟩
  step with extra_ser as ⟨ b3, hb3 ⟩
  step with lenenc_rawint_ser as ⟨ b4, hb4 ⟩
  step with ser_bitmap h64 as ⟨ b5, hb5 ⟩
  step with ser_bitmap h64 as ⟨ b6, hb6 ⟩
  step with eof_ser as ⟨ b7, hb7 ⟩
  rw [hb7, hb6, hb5, hb4, hb3, hb2, hb1]; unfold rowsEnc; split_ifs <;> simp

/-! ## Lengths -/

theorem lenencInt_length_le (n : Nat) : (lenencInt n).length ≤ 9 := by
  unfold lenencInt; split_ifs <;> simp

theorem cast_small (x : U64) (h : x.val ≤ Usize.max) : (UScalar.cast UScalarTy.Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (usize_lt_of_le_max h)

theorem sat_val (x y : Usize) : (core.num.Usize.saturating_add x y).val = min (x.val + y.val) Usize.max := by
  have := usize_sat_add x y
  simpa [lift] using this

theorem cast_u16max : (UScalar.cast UScalarTy.Usize core.num.U16.MAX).val = 65535 := by
  simp [UScalar.cast_val_eq, core.num.U16.MAX]
  rcases System.Platform.numBits_eq with h | h <;> simp [h, U16.rMax]

theorem cast_u32max : (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
  simp [UScalar.cast_val_eq, core.num.U32.MAX]
  rcases System.Platform.numBits_eq with h | h <;> simp [h, U32.rMax]

set_option maxHeartbeats 2000000 in
theorem rows_event_len_spec (nc : U64) (exl : Usize) (hb ha : Bool) (rdl : Usize)
    (hbl : hb = true ∨ ha = true → (nc.val + 7) / 8 ≤ Usize.max) :
    binlog.events.rows_event.rows_event_len nc exl hb ha rdl ⦃ n => n.val =
      min (6 + 2 + 2 + min exl.val 65533 + (lenencInt nc.val).length +
        (if hb then (nc.val + 7) / 8 else 0) + (if ha then (nc.val + 7) / 8 else 0) + rdl.val) evLenCap ⦄ := by
  unfold binlog.events.rows_event.rows_event_len
  have hcap := usize_max_ge_cap
  step*
  · rw [i_post, cast_u16max]; simp
  step with misc.lenenc_int_len_spec as ⟨ i3, hi3 ⟩
  step*
  have hl9 := lenencInt_length_le nc.val
  have hi : i.val = 65535 := by rw [i_post, cast_u16max]
  have hi4 : i4.val = (lenencInt nc.val).length := by rw [i4_post, cast_small _ (by omega), hi3]
  have hdc : i5.val = (nc.val + 7) / 8 := by rw [i5_post, Nat.ceilDiv_eq_add_pred_div]; rfl
  have hbm : hb = true ∨ ha = true → bitmap_len.val = (nc.val + 7) / 8 := by
    intro hh; rw [bitmap_len_post, cast_small _ (by have := hbl hh; omega), hdc]
  have hcp : (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := cast_u32max
  have hL : binlog.events.BinlogEventHeader.LEN.val = 19 := by simp [binlog.events.BinlogEventHeader.LEN]
  have hsat := fun (x y : Usize) => (sat_val x y)
  cases hb <;> cases ha <;> simp only [Bool.false_eq_true, ↓reduceIte, true_or, or_true, forall_const] at hbm ⊢ <;> step* <;>
    simp only [hsat, i6_post, hcp, hL, hi4, hbm, hi, len_post, len1_post, len2_post, len3_post, len4_post, i2_post, i1_post, evLenCap] at * <;> omega


theorem bare65533_max : (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65533#usize).MAX_LEN = ok 65533#usize := by
  show ok (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN 65533#usize) = _
  rw [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]

theorem rows_len_gen (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion)
    (hbl : e.columns_before_image.isSome = true ∨ e.columns_after_image.isSome = true →
      (e.num_columns.1.val + 7) / 8 ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.len
  have hnc : binlog.events.rows_event.RowsEvent.impl.num_columns e = ok e.num_columns.1 := rfl
  simp only [hnc, bind_ok]
  step with misc.raw.bytes.RawBytes.len_spec _ 65533#usize bare65533_max as ⟨ exl, hexl ⟩
  step with misc.raw.bytes.RawBytes.len_spec misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple _ rfl as ⟨ rdl, hrdl ⟩
  have hm := misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  have hc := PKUtil.cowList_length_le e.rows_data.1
  apply WP.spec_mono (rows_event_len_spec _ _ _ _ _ (by simpa using hbl))
  intro n hn
  rw [hn, rowsLenCrate, hexl, hrdl, hm, Nat.min_eq_left hc]
  cases e.columns_before_image <;> cases e.columns_after_image <;> simp

theorem bm_len (o : Option (misc.raw.bytes.RawBytes misc.raw.bytes.BareBitmapBytes Usize)) (bl : Nat) (c : Bool)
    (hbl : bl ≤ 2 ^ 61) (h : o.map (fun b => (cowList b.1).length) = (if c then some bl else none)) :
    ((o.map (fun b => (cowList b.1).take (2 ^ 61))).getD []).length = (if o.isSome then bl else 0) ∧
      (o.isSome = true → bl ≤ Usize.max) := by
  cases o with
  | none => simp
  | some b =>
    have hb := PKUtil.cowList_length_le b.1
    cases c <;> simp at h ⊢
    refine ⟨by omega, by omega⟩

theorem bl_le (n : U64) : (n.val + 7) / 8 ≤ 2 ^ 61 := by
  have := n.hBounds; simp at this; omega

theorem rows_consistent_bm (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) :
    ((e.columns_before_image.map (fun b => (cowList b.1).take (2 ^ 61))).getD []).length =
        (if e.columns_before_image.isSome then (e.num_columns.1.val + 7) / 8 else 0) ∧
    ((e.columns_after_image.map (fun b => (cowList b.1).take (2 ^ 61))).getD []).length =
        (if e.columns_after_image.isSome then (e.num_columns.1.val + 7) / 8 else 0) ∧
    (e.columns_before_image.isSome = true ∨ e.columns_after_image.isSome = true →
      (e.num_columns.1.val + 7) / 8 ≤ Usize.max) := by
  obtain ⟨_, _, hb, ha⟩ := hc
  have h1 := bm_len _ _ _ (bl_le _) hb
  have ha' : e.columns_after_image.map (fun b => (cowList b.1).length) =
      if (!rowsIsDelete e.event_type) = true then some ((e.num_columns.1.val + 7) / 8) else none := by
    rw [ha]; cases rowsIsDelete e.event_type <;> rfl
  have h2 := bm_len _ _ _ (bl_le _) ha'
  refine ⟨h1.1, h2.1, ?_⟩
  rintro (h | h)
  · exact h1.2 h
  · exact h2.2 h

theorem rowsLenCrate_v2 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h2 : rowsIsV2 e.event_type = true) :
    rowsLenCrate e = min (rowsEnc e).length evLenCap := by
  obtain ⟨hb, ha, _⟩ := rows_consistent_bm e hc
  simp only [rowsLenCrate, rowsEnc, h2, ↓reduceIte, List.length_append, hb, ha, length_leBytes, List.length_take]
  omega

theorem rowsLenCrate_v1' (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) : rowsLenCrate e = (rowsEnc e).length + 2 := by
  obtain ⟨hb, ha, _⟩ := rows_consistent_bm e hc
  have hex : cowList e.extra_data.1 = [] := hc.2.1 h1
  simp only [rowsEnc, h1, Bool.false_eq_true, ↓reduceIte, List.length_append, hb, ha, length_leBytes, List.length_nil] at hcap ⊢
  simp only [rowsLenCrate, hex, List.length_nil]
  omega

end mysql_common.BERUtil
