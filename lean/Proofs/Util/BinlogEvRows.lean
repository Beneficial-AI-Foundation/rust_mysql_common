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
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Defs.LemmasBinlogEvents
import Proofs.Defs.LemmasCF

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

theorem cast_u8max : (UScalar.cast UScalarTy.Usize core.num.U8.MAX).val = 255 := by
  simp [UScalar.cast_val_eq, core.num.U8.MAX]
  rcases System.Platform.numBits_eq with h | h <;> simp [h, U8.rMax]

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

/-! ## Table map -/

theorem json_loop (s : Slice U8) (count i : Usize) (hi : i.val ≤ s.length) (hc : count.val ≤ i.val) :
    binlog.events.table_map_event.count_json_columns_loop s count i ⦃ r =>
      r.val = count.val + (s.val.drop i.val).countP (fun b => b.val = 245) ⦄ := by
  unfold binlog.events.table_map_event.count_json_columns_loop
  apply loop.spec_decr_nat (fun x : Usize × Usize => s.length - x.2.val)
    (fun x => x.2.val ≤ s.length ∧ x.1.val ≤ x.2.val ∧
      x.1.val + (s.val.drop x.2.val).countP (fun b => b.val = 245) = count.val + (s.val.drop i.val).countP (fun b => b.val = 245))
  · rintro ⟨c, j⟩ ⟨h1, h2, h3⟩
    unfold binlog.events.table_map_event.count_json_columns_loop.body
    simp only at h1 h2 h3
    step*
    · have hj : j.val < s.val.length := by scalar_tac
      have hi4 : i4.val = 245 := by rw [i4_post]; simp [UScalar.cast_val_eq, i3_post]
      have hd : s.val.drop j.val = s.val[j.val] :: s.val.drop (j.val+1) := List.drop_eq_getElem_cons hj
      rw [hd] at h3
      have hsl : s.length = s.val.length := rfl
      split
      · rename_i heq
        have h245 : (s.val[j.val]).val = 245 := by rw [← i2_post, heq, hi4]
        step*
        simp only [List.countP_cons, h245, decide_true, ↓reduceIte] at h3
        refine ⟨by omega, by omega, by rw [i5_post, count1_post]; omega, by omega⟩
      · rename_i hne
        have h245 : ¬ (s.val[j.val]).val = 245 := by
          intro h; apply hne; rw [i2_post]; exact UScalar.eq_of_val_eq (by rw [h, hi4])
        step*
        simp only [List.countP_cons, h245, decide_false, Bool.false_eq_true, ↓reduceIte] at h3
        refine ⟨by omega, by omega, by rw [i5_post]; omega, by omega⟩
    · have hj : s.val.length ≤ j.val := by scalar_tac
      rw [List.drop_eq_nil_of_le hj] at h3
      simp at h3; omega
  · exact ⟨hi, hc, rfl⟩

theorem patA (ptr : Slice U8) (k : Usize) (m : Nat) (hk : k.val = m) :
    (do
      let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) ptr { «end» := k }
      match o with
      | none => ok none
      | some x => ok (some (x, k))) ⦃ o =>
      o.map (fun p => (p.1.val, p.2.val)) = (takeExact m ptr.val).map (fun p => (p.1, m)) ∧
      ∀ p ∈ o, p.2.val ≤ ptr.length ⦄ := by
  simp only [core.slice.Slice.get, 
    core.slice.index.SliceIndexRangeToUsizeSlice.get]
  subst hk
  by_cases h : k ≤ ptr.length
  · have h' : k.val ≤ ptr.val.length := h
    simp [h, takeExact, List.slice, Slice.length]
  · have h' : ¬ k.val ≤ ptr.val.length := h
    simp [h, takeExact]

theorem patB (ptr : Slice U8) :
    (do
      let s ← lift (Array.to_slice (Std.Array.empty U8))
      ok (some (s, 0#usize))) ⦃ o =>
      o.map (fun p => (p.1.val, p.2.val)) = (takeExact 0 ptr.val).map (fun p => (p.1, 0)) ∧
      ∀ p ∈ o, p.2.val ≤ ptr.length ⦄ := by
  simp [lift, takeExact, Array.to_slice, Std.Array.empty]

theorem get_metadata_spec : ∀ (n : Nat) (t : constants.ColumnType) (ptr : Slice U8) (isArr : Bool), ptr.length = n →
    binlog.ColumnType.get_metadata t ptr isArr ⦃ o =>
      o.map (fun p => (p.1.val, p.2.val)) = tmColumnMeta isArr (columnTypeCode t) ptr.val ∧
      ∀ p ∈ o, p.2.val ≤ ptr.length ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ptr isArr hn
  have key := tmColumnMeta.eq_def isArr (columnTypeCode t) ptr.val
  rw [(columnTypeOfCode_columnTypeCode t).2] at key
  simp only [key]
  rw [binlog.ColumnType.get_metadata.eq_def]
  cases t <;> simp only [columnTypeCode, getMetadataLen, Nat.reduceEqDiff, ↓reduceIte]
  case MYSQL_TYPE_DECIMAL | MYSQL_TYPE_TINY | MYSQL_TYPE_SHORT | MYSQL_TYPE_LONG | MYSQL_TYPE_NULL | MYSQL_TYPE_TIMESTAMP | MYSQL_TYPE_LONGLONG | MYSQL_TYPE_INT24 | MYSQL_TYPE_DATE | MYSQL_TYPE_TIME | MYSQL_TYPE_DATETIME | MYSQL_TYPE_YEAR | MYSQL_TYPE_NEWDATE | MYSQL_TYPE_UNKNOWN | MYSQL_TYPE_VAR_STRING => exact patB ptr
  case MYSQL_TYPE_FLOAT | MYSQL_TYPE_DOUBLE | MYSQL_TYPE_TIMESTAMP2 | MYSQL_TYPE_DATETIME2 | MYSQL_TYPE_TIME2 | MYSQL_TYPE_VECTOR | MYSQL_TYPE_JSON | MYSQL_TYPE_TINY_BLOB | MYSQL_TYPE_MEDIUM_BLOB | MYSQL_TYPE_LONG_BLOB | MYSQL_TYPE_BLOB | MYSQL_TYPE_GEOMETRY => exact patA ptr _ _ rfl
  case MYSQL_TYPE_BIT | MYSQL_TYPE_NEWDECIMAL | MYSQL_TYPE_ENUM | MYSQL_TYPE_SET | MYSQL_TYPE_STRING => exact patA ptr _ _ rfl
  case MYSQL_TYPE_VARCHAR => cases isArr <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact patA ptr _ _ rfl
  case MYSQL_TYPE_TYPED_ARRAY =>
    simp only [core.slice.Slice.first, bind_ok]
    rcases hp : ptr.val with _ | ⟨e, rest⟩
    · simp
    · simp only [List.head?_cons, constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec, bind_ok]
      have hk := tmColumnMeta.eq_def true e.val rest
      rcases hc : columnTypeOfCode e.val with _ | ty
      · simp only [hc] at hk; simp [hk]
      · have hcode : columnTypeCode ty = e.val := by
          have := List.find?_some hc; simpa using this
        have hl1 : (1#usize).val ≤ ptr.length := by simp [Slice.length, hp]
        simp only [core.slice.Slice.get,
          core.slice.index.SliceIndexRangeFromUsizeSlice.get, hl1, ↓reduceIte, bind_ok]
        have hd : (ptr.drop 1#usize).val = rest := by simp [Slice.drop, hp]
        have hdl : (ptr.drop 1#usize).length < n := by simp [Slice.length, hd] at hn ⊢; simp [hp] at hn; omega
        apply WP.spec_bind (ih _ hdl ty (ptr.drop 1#usize) true rfl)
        rintro o2 ⟨h1, h2⟩
        rw [hcode, hd] at h1
        cases o2 with
        | none => simp at h1; simp [← h1]
        | some p =>
          obtain ⟨x, k⟩ := p
          simp at h1 h2
          step*
          have hpl : ptr.length = (ptr.val).length := rfl
          rw [← h1]; simp [i_post]; omega

theorem cmf_spec : ∀ (k : Nat) (cs : misc.raw.seq.RawSeq U8 constants.ColumnType U8) (md : Slice U8) (i off col : Usize),
    col.val - i.val = k → i.val ≤ col.val → off.val ≤ md.length →
    binlog.events.table_map_event.column_metadata_from cs md i off col ⦃ o =>
      o.map (·.val) = tmMetaAt ((cowList cs.1).drop i.val) (md.val.drop off.val) (col.val - i.val) ⦄ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro cs md i off col hk hic hoff
  rw [binlog.events.table_map_event.column_metadata_from.eq_def]
  step with misc.raw.seq.RawSeq.get_spec as ⟨ o, ho ⟩
  cases o with
  | none =>
    simp at ho
    simp [List.drop_eq_nil_of_le ho, tmMetaAt]
  | some x =>
    simp at ho
    have hlt : i.val < (cowList cs.1).length := by
      by_contra hh; rw [List.getElem?_eq_none (by omega)] at ho; simp at ho
    have hdrop : (cowList cs.1).drop i.val = x.1 :: (cowList cs.1).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]; congr; rw [List.getElem?_eq_getElem hlt] at ho; simp at ho; exact ho.symm
    rw [hdrop]
    simp only [misc.raw._const.RawConst.get_eq, constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec, bind_ok]
    have hk2 := tmColumnMeta.eq_def false x.1.val (md.val.drop off.val)
    rcases hc : columnTypeOfCode x.1.val with _ | ty
    · simp only [hc] at hk2; simp [tmMetaAt, hk2]
    · have hcode : columnTypeCode ty = x.1.val := by
        have := List.find?_some hc; simpa using this
      have hoff' : off ≤ md.length := hoff
      simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeFromUsizeSlice.get, hoff', ↓reduceIte, bind_ok]
      apply WP.spec_bind (get_metadata_spec _ ty (md.drop off) false rfl)
      rintro o2 ⟨h1, h2⟩
      have hdv : (md.drop off).val = md.val.drop off.val := by simp [Slice.drop]
      rw [hcode, hdv] at h1
      cases o2 with
      | none => simp at h1; simp [tmMetaAt, ← h1]
      | some p =>
        obtain ⟨mt, len⟩ := p
        simp at h1 h2
        simp only [tmMetaAt, ← h1]
        split
        · rename_i heq
          have : col.val - i.val = 0 := by rw [heq]; simp
          simp [this]
        · rename_i hne
          have hne' : i.val ≠ col.val := fun h => hne (UScalar.eq_of_val_eq h)
          have h0 : col.val - i.val ≠ 0 := by omega
          simp only [h0, ↓reduceIte]
          have hml : md.length = md.val.length := rfl
          have hmx := md.property
          step as ⟨ i1, i1_post ⟩
          step as ⟨ i2, i2_post ⟩
          have hrec := ih (col.val - i1.val) (by omega) cs md i1 i2 col rfl (by omega) (by omega)
          apply WP.spec_mono hrec
          intro r hr
          rw [hr, i1_post, i2_post]
          simp [List.drop_drop]
          congr 1

theorem col_meta_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_column_metadata e i ⦃ o =>
      o.map (·.val) = tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.get_column_metadata
  step with PKUtil.lenenc_as_bytes_spec as ⟨ s, hs ⟩
  apply WP.spec_mono (cmf_spec _ e.columns_type s 0#usize 0#usize i rfl (by simp) (by simp))
  intro o ho
  simpa [hs] using ho

theorem tmMetaAt_string : ∀ (tys md : List U8) (i : Nat) (m : List U8) (b : U8),
    tmMetaAt tys md i = some m → tys[i]? = some b → b.val = 254 → m.length = 2 := by
  intro tys
  induction tys with
  | nil => intro md i m b h; simp [tmMetaAt] at h
  | cons ty tys ih =>
    intro md i m b h hb h254
    simp only [tmMetaAt] at h
    rcases hm : tmColumnMeta false ty.val md with _ | ⟨m', k⟩
    · simp [hm] at h
    · simp only [hm] at h
      cases i with
      | zero =>
        simp at h hb
        subst hb h
        have := tmColumnMeta.eq_def false ty.val md
        rw [hm, h254] at this
        simp [columnTypeOfCode, allColumnTypes, columnTypeCode, getMetadataLen, takeExact] at this
        obtain ⟨⟨x, hx⟩, _⟩ := this
        by_cases hl : 2 ≤ md.length
        · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hx; rw [← hx.1]; simp; omega
        · simp [hl] at hx
      | succ i =>
        simp at h hb
        exact ih _ _ _ _ h hb h254

theorem real_string_spec (rt f1 : U8) (hrt : rt.val = 254) :
    binlog.events.table_map_event.real_string_type rt f1 ⦃ r =>
      match tmStringRealType f1.val with
      | some t => r = .Ok t
      | none => r = .Err (.Unexpected (byte (f1.val ||| 0x30))) ⦄ := by
  unfold binlog.events.table_map_event.real_string_type
  have hrt' : rt = 254#u8 := UScalar.eq_of_val_eq (by simp [hrt])
  subst hrt'
  by_cases h0 : f1 = 0#u8
  · subst h0; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact (WP.spec_ok _).mpr rfl
  · have h0' : f1.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simp [h]))
    simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true, ↓reduceIte, bind_ok, tmStringRealType, h0']
    generalize hv : f1 ||| 48#u8 = v
    have hvv : v.val = f1.val ||| 0x30 := by rw [← hv]; simp
    split
    · have : f1.val ||| 48 = 247 := by rw [← hvv]; rfl
      simp [this]
    · have : f1.val ||| 48 = 248 := by rw [← hvv]; rfl
      simp [this]
    · have : f1.val ||| 48 = 254 := by rw [← hvv]; rfl
      simp [this]
    · rename_i n1 n2 n3
      have a1 : v.val ≠ 247 := fun h => n1 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a2 : v.val ≠ 248 := fun h => n2 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a3 : v.val ≠ 254 := fun h => n3 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      rw [← hvv]
      simp [a1, a2, a3, PCSUtil.byte_eq_self]

theorem real_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) (t : constants.ColumnType)
    (hS : columnTypeCode t = 254 → ∀ m, tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val = some m → m ≠ []) :
    binlog.events.table_map_event.TableMapEvent.get_real_type e i t ⦃ r =>
      if columnTypeCode t = 10 then r = .Ok .MYSQL_TYPE_NEWDATE
      else if columnTypeCode t = 254 then
        match tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val with
        | none => r = .Ok t
        | some m => match tmStringRealType (m.headD (byte 0)).val with
          | some t' => r = .Ok t'
          | none => r = .Err (.Unexpected (byte ((m.headD (byte 0)).val ||| 0x30)))
      else r = .Ok t ⦄ := by
  cases t
  case MYSQL_TYPE_STRING =>
    simp only [columnTypeCode] at hS ⊢
    simp only [binlog.events.table_map_event.TableMapEvent.get_real_type, Nat.reduceEqDiff, ↓reduceIte]
    step*
    step with col_meta_spec as ⟨ o, ho ⟩
    cases o with
    | none => simp at ho; simp [← ho]
    | some mb =>
      simp at ho
      have hne := hS trivial _ ho.symm
      have h0 : 0 < mb.length := by
        simp [Slice.length]; exact List.length_pos_iff.mpr hne
      step*
      rw [← ho]
      have hrt : real_type.val = 254 := by rw [real_type_post]; rfl
      apply WP.spec_mono (real_string_spec real_type i hrt)
      intro r hr
      rcases hm : mb.val with _ | ⟨a, l⟩
      · exact absurd hm hne
      · simp only [hm] at i_post ⊢; simp at i_post; subst i_post; simpa using hr
  all_goals simp [binlog.events.table_map_event.TableMapEvent.get_real_type, columnTypeCode]

/-! ## Table map length -/

theorem uadd_overflow' {ty : UScalarTy} (x y : UScalar ty) (h : 2 ^ ty.numBits ≤ x.val + y.val) :
    x + y = fail .integerOverflow := by
  show UScalar.add x y = _
  simp only [UScalar.add, UScalar.tryMk]
  have := UScalar.tryMkOpt_eq ty (x.val + y.val)
  cases hc : UScalar.tryMkOpt ty (x.val + y.val) with
  | none => rfl
  | some z => rw [hc] at this; exfalso; simp [UScalar.inBounds] at this; omega

theorem lsl_cases (s : Slice U8) :
    (∃ v, misc.lenenc_str_len s = ok v ∧ v.val = (lenencStr s.val).length) ∨
      misc.lenenc_str_len s = fail .integerOverflow := by
  by_cases h : (lenencStr s.val).length < 2 ^ 64
  · left; exact PBUtil.spec_eq_ok (misc.lenenc_str_len_spec s h)
  · right
    unfold misc.lenenc_str_len
    have hs : s.val.length < 2 ^ 64 := lt_two_pow_64_of_le_max s.property
    have hl : (UScalar.cast UScalarTy.U64 (Slice.len s)).val = s.val.length := by
      rw [UScalar.cast_val_eq]; simp [Slice.len]; simpa using hs
    obtain ⟨i1, h1, hi1⟩ := PBUtil.spec_eq_ok (misc.lenenc_int_len_spec (UScalar.cast UScalarTy.U64 (Slice.len s)))
    rw [hl] at hi1
    have ho := uadd_overflow' i1 (UScalar.cast UScalarTy.U64 (Slice.len s)) (by
      rw [hl, hi1]; simp [lenencStr] at h; simp; omega)
    simp [lift, h1, ho]

theorem tm_len_gen (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion)
    (hn : e.columns_count.1.val + 8 < 2 ^ 64) (hm : (lenencStr (cowList e.columns_metadata.1)).length < 2 ^ 64) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = tmLenCrate e ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hcap := usize_max_ge_cap
  have hmax : Usize.max = 2 ^ 64 - 1 := by simp [Target64] at h64; simp [Usize.max, Usize.numBits, h64]
  have hcc : binlog.events.table_map_event.TableMapEvent.impl.columns_count e = ok e.columns_count.1 := rfl
  simp only [hcc, bind_ok]
  obtain ⟨tid, fl, ⟨c, u⟩, n1, ⟨c1, u1⟩, n2, cc, ct, md, nb, om⟩ := e
  simp only at hn hm ⊢
  step*
  step with misc.lenenc_int_len_spec as ⟨ i6, hi6 ⟩
  step*
  step with misc.lenenc_str_len_spec _ (by rw [s2_post]; exact hm) as ⟨ i9, hi9 ⟩
  step*
  step with misc.raw.bytes.RawBytes.len_spec misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple _ rfl as ⟨ i14, hi14 ⟩
  step*
  · rw [i15_post, cast_u32max]; simp [binlog.events.BinlogEventHeader.LEN]
  · have hL : binlog.events.BinlogEventHeader.LEN.val = 19 := by simp [binlog.events.BinlogEventHeader.LEN]
    have h1 : i1.val = 255 := by rw [i1_post, cast_u8max]
    have h4 : i4.val = 255 := by rw [i4_post, cast_u8max]
    have h15 : i15.val = 2 ^ 32 - 1 := by rw [i15_post, cast_u32max]
    have hl9 := lenencInt_length_le cc.1.val
    have h7 : i7.val = (lenencInt cc.1.val).length := by rw [i7_post, cast_small _ (by omega), hi6]
    have h8 : i8.val = cc.1.val := by rw [i8_post, PBUtil.cast_usize_64 h64]
    have h11 : i11.val = cc.1.val := by rw [i11_post, PBUtil.cast_usize_64 h64]
    have h10 : i10.val = (lenencStr (cowList md.1)).length := by
      rw [i10_post, cast_small _ (by rw [hi9, s2_post]; omega), hi9, s2_post]
    have hom := PKUtil.cowList_length_le om.1
    have hEM := misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
    have hs : s.len.val = (cowList c).length := by simp [Slice.len, ← s_post]
    have hs1 : s1.len.val = (cowList c1).length := by simp [Slice.len, ← s1_post]
    simp only [tmLenCrate, evLenCap]
    rw [hEM] at hi14
    have hdb := min_le_right (cowList c).length 255
    have htb := min_le_right (cowList c1).length 255
    have e2 : len2.val = 9 := by clear * - len_post len1_post len2_post hcap; omega
    have e3 : len3.val = 9 + min (cowList c).length 255 := by
      rw [len3_post, i2_post, hs, h1, e2]; clear * - hcap; omega
    have e5 : len5.val = 11 + min (cowList c).length 255 := by
      rw [len5_post, len4_post, e3]; clear * - hcap; omega
    have e7 : len7.val = 12 + min (cowList c).length 255 + min (cowList c1).length 255 := by
      rw [len7_post, len6_post, i5_post, hs1, h4, e5]; clear * - hcap; omega
    have e8 : len8.val = 6 + 2 + 1 + min (cowList c).length 255 + 1 + 1 + min (cowList c1).length 255 + 1 +
        (lenencInt cc.1.val).length := by
      rw [len8_post, h7, e7]; clear * - hcap hl9; omega
    have key : ∀ (a b c d f M K : Nat), K ≤ M →
        min (min (min (min (min (a + b) M + c) M + d) M + f) M) K = min (a + b + c + d + f) K := by
      intros; omega
    have hK : i16.val ≤ Usize.max := by rw [i16_post, h15, hL]; clear * - hcap; omega
    rw [n_post, len12_post, len11_post, len10_post, len9_post, key _ _ _ _ _ _ _ hK]
    rw [e8, h8, h10, i13_post, i12_post, h11, hi14, Nat.min_eq_left hom, i16_post, h15, hL]

theorem tm_len_panics (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion)
    (hn : 2 ^ 64 ≤ e.columns_count.1.val + 8) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = fail .integerOverflow := by
  unfold binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  have hcc : binlog.events.table_map_event.TableMapEvent.impl.columns_count e = ok e.columns_count.1 := rfl
  simp only [hcc, bind_ok]
  obtain ⟨tid, fl, ⟨c, u⟩, n1, ⟨c1, u1⟩, n2, cc, ct, md, nb, om⟩ := e
  simp only at hn ⊢
  obtain ⟨s, hs, -⟩ := PBUtil.spec_eq_ok (cow_deref_spec core.clone.CloneU8 c)
  obtain ⟨s1, hs1, -⟩ := PBUtil.spec_eq_ok (cow_deref_spec core.clone.CloneU8 c1)
  obtain ⟨i6, hi6, -⟩ := PBUtil.spec_eq_ok (misc.lenenc_int_len_spec cc.1)
  obtain ⟨s2, hs2, -⟩ := PBUtil.spec_eq_ok (PKUtil.lenenc_as_bytes_spec md)
  have hadd : UScalar.cast UScalarTy.Usize cc.1 + 8#usize = fail .integerOverflow :=
    uadd_overflow' _ _ (by
      rw [PBUtil.cast_usize_64 h64]; simp [Target64] at h64; simp [UScalarTy.numBits, h64]; omega)
  rcases lsl_cases s2 with ⟨i9, h9, -⟩ | h9 <;>
    simp [hs, hs1, hi6, hs2, h9, lift, hadd]

end mysql_common.BERUtil
