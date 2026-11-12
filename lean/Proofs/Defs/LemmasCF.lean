import Defs

/-! Sanity properties of the stage c–f definitions in `Defs/` (pure Lean, no Rust): the readers
invert the encoders, and the encoders have the shapes the protocol pages describe. They are not
spec statements, but reviewers can use them to check that the definitions mean what they say.
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- Every column type's code is a byte, and decodes back to it. -/
theorem columnTypeOfCode_columnTypeCode (ct : constants.ColumnType) :
    columnTypeCode ct < 256 ∧ columnTypeOfCode (columnTypeCode ct) = some ct := by
  sorry

/-- A NULL bitmap has `nullBitmapLen` bytes, and its bit for field `i` is `nulls[i]`. -/
theorem nullBitmap_spec (off : Nat) (nulls : List Bool) :
    (nullBitmap off nulls).length = nullBitmapLen off nulls.length ∧
    ∀ i, bitmapBit off (nullBitmap off nulls) i = nulls.getD i false := by
  sorry

/-- An empty payload is one empty chunk. -/
theorem frame_nil (seq : Nat) : frame seq [] = [byte 0, byte 0, byte 0, byte seq] := by
  sorry

/-- A payload shorter than `2^24 - 1` is one chunk. -/
theorem frame_short (seq : Nat) (p : List U8) (h : p.length < maxPayloadLen) :
    frame seq p = leBytes 3 p.length ++ byte seq :: p := by
  sorry

/-- The chunks of a payload: its bytes plus a 4-byte header per chunk. -/
theorem frame_length (seq : Nat) (p : List U8) :
    (frame seq p).length = p.length + 4 * frameCount p.length := by
  sorry

/-- The crate's packet reader reads back the chunks of a payload (the reference version of the
    codec round trip in `Specs/Proto/Codec.lean`). -/
theorem plainDecode_frame (seq : U8) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max)
    (comp : Option U8) :
    plainDecode seq .idle (frame seq.val p ++ tail) [] max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p) := by
  sorry

/-- The crate's column definition reader reads back the protocol layout (fields in range). -/
theorem colDefRead_colDefEnc (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEnc c ++ t) = (some c, t) := by
  sorry

/-- The text-row reader reads back a row of `NULL`s and byte strings. -/
theorem textRowRead_textEnc (vs : List Val) (hv : ∀ v ∈ vs, isTextVal v = true)
    (hs : ∀ s, Val.bytes s ∈ vs → s.length < 2 ^ 64) (t : List U8) :
    textRowRead vs.length ((vs.map textEnc).flatten ++ t) = (some vs, t) := by
  sorry

/-- The ERR packet reader reads back a packet that fits the capabilities. -/
theorem errPacketRead_errPacketEnc (caps : Nat) (e : ErrPkt) (hc : errCompatible caps e)
    (hcode : ∀ code st msg, e = .error code st msg → code < 2 ^ 16 ∧ ∀ s, st = some s → s.length = 5)
    (hp : ∀ p, e = .progress p → p.stage < 256 ∧ p.maxStage < 256 ∧ p.info.length < 2 ^ 64) :
    errPacketRead caps (errPacketEnc e) = (some e, []) := by
  sorry

end Defs
