import Defs

/-! Statements for `impl BytesRepr for FixedLengthText<LEN>` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `FixedLengthText<LEN>::MAX_LEN`: `LEN`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN L = L := by
  sorry

/-- `FixedLengthText<LEN>::SIZE` is `Some(LEN)`. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE L = some L := by
  sorry

/-- `FixedLengthText<LEN>::serialize`: appends exactly `LEN` bytes: the text, truncated or right-padded with `0x00` (documented). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (L : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + L.val ≤ Usize.max) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize L text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ⦄ := by
  sorry

/-- `FixedLengthText<LEN>::deserialize`: the next `LEN` bytes, padding included. Unchecked (`SIZE` is `Some(LEN)`, so it uses `eat`): panics on a shorter buffer (`deserialize_panics`); `parse` checks (`parse_rawbytes_spec`). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (L : Usize) (buf : io.ParseBuf) (h : L.val ≤ buf.length) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ r rest =>
      (okPart r).map cowList = some (buf.val.take L.val) ∧ rest.val = buf.val.drop L.val ⦄ := by
  sorry

/-- `FixedLengthText<LEN>::deserialize` panics on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_panics (L : Usize) (buf : io.ParseBuf) (h : buf.length < L.val) :
    ¬ misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<RawBytes<FixedLengthText<LEN>>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.parse_rawbytes_spec (L : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      if L.val ≤ buf.length then
        (okPart r).map (fun rb => cowList rb.1) = some (buf.val.take L.val) ∧
        rest.val = buf.val.drop L.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- Round trip through `parse::<RawBytes<FixedLengthText<LEN>>>`: what `serialize` writes comes back padded/truncated to exactly `LEN` bytes (so it is the original text iff the text has `LEN` bytes). -/
theorem misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (L : Usize) (text tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ++ tail) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      (okPart r).map (fun rb => cowList rb.1) =
        some (text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0)) ∧
      rest.val = tail ⦄ := by
  sorry

end mysql_common
