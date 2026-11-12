import Defs

/-! Statements for `struct NullBitmap and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ClientSide::BIT_OFFSET` is 0 (from `src/value/mod.rs`; the offset of `COM_STMT_EXECUTE` bitmaps). -/
theorem value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val :
    value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET.val = 0 := by
  sorry

/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>`: `SIZE` is `None`. -/
theorem packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (inst : value.SerializationSide T) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE inst = none := by
  sorry

/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>` with context the number of columns: total; the next `bitmap_len` bytes, or an error with the buffer unchanged if there are fewer. -/
theorem packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize inst n buf ⦃ r rest =>
      if nullBitmapLen off.val n.val ≤ buf.length then
        (okPart r).map (fun bm => cowList bm.1) = some (buf.val.take (nullBitmapLen off.val n.val)) ∧
        rest.val = buf.val.drop (nullBitmapLen off.val n.val)
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `new`: an all-clear bitmap of `bitmap_len` bytes. -/
theorem packets.NullBitmapTVecU8.new_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmapTVecU8.new inst n ⦃ bm =>
      bm.1.val = List.replicate (nullBitmapLen off.val n.val) (byte 0) ⦄ := by
  sorry

/-- `read`: the first `bitmap_len` bytes of `input`, and the rest. -/
theorem packets.NullBitmapTVecU8.read_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : nullBitmapLen off.val n.val ≤ input.length) :
    packets.NullBitmapTVecU8.read inst input n ⦃ bm rest =>
      bm.1.val = input.val.take (nullBitmapLen off.val n.val) ∧
      rest.val = input.val.drop (nullBitmapLen off.val n.val) ⦄ := by
  sorry

/-- `read` panics (`assert!`) on an input shorter than `bitmap_len`. -/
theorem packets.NullBitmapTVecU8.read_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : input.length < nullBitmapLen off.val n.val) :
    ¬ packets.NullBitmapTVecU8.read inst input n ⦃ _ => True ⦄ := by
  sorry

/-- `bitmap_len`: `(n + 7 + BIT_OFFSET) / 8`. -/
theorem packets.NullBitmap.bitmap_len_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmap.bitmap_len inst asRef n ⦃ r => r.val = nullBitmapLen off.val n.val ⦄ := by
  sorry

/-- `from_bytes`: wraps the bytes. -/
theorem packets.NullBitmap.from_bytes_eq {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8)) (bytes : U) :
    packets.NullBitmap.from_bytes inst asRef bytes = ok (bytes, ()) := by
  sorry

/-- `is_null(i)`: bit `i + BIT_OFFSET` of the bytes, for any byte container `U` (given its bytes `s`). -/
theorem packets.NullBitmap.is_null_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : (i.val + off.val) / 8 < s.length) :
    packets.NullBitmap.is_null inst asRef self i ⦃ b => b = bitmapBit off.val s.val i.val ⦄ := by
  sorry

/-- `is_null(i)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
theorem packets.NullBitmap.is_null_panics {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : s.length ≤ (i.val + off.val) / 8) :
    ¬ packets.NullBitmap.is_null inst asRef self i ⦃ _ => True ⦄ := by
  sorry

/-- `set(i, is_null)` (at `Vec<u8>`): sets bit `i + BIT_OFFSET` to `is_null`, every other bit unchanged. -/
theorem packets.NullBitmap.set_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : (i.val + off.val) / 8 < self.1.length) :
    packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b ⦃ bm =>
      bm.1.length = self.1.length ∧
      ∀ pos, bitAt bm.1.val pos = if pos = i.val + off.val then b else bitAt self.1.val pos ⦄ := by
  sorry

/-- `set(i, _)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
theorem packets.NullBitmap.set_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : self.1.length ≤ (i.val + off.val) / 8) :
    ¬ packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b ⦃ _ => True ⦄ := by
  sorry

/-- `AsRef<[u8]> for NullBitmap`: the bytes. -/
theorem packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref_eq {T U : Type} (asRef : core.convert.AsRef U (Slice U8)) (self : packets.NullBitmap T U) :
    packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref asRef self = asRef.as_ref self.1 := by
  sorry

end mysql_common
