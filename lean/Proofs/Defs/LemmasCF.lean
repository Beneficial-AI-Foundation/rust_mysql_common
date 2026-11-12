import Defs

/-! Facts about the stage c–f definitions (spec file: `Specs/DefsCF.lean`). Proofs: TODO. -/

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

/-- The binary value decoder reads back a `Value` encoded at its column's type (`binEncAt`), when it fits the column (`binFitsAt`), up to `binNormAt`. -/
theorem binRead_binEncAt (ct : constants.ColumnType) (unsigned : Bool) (v : value.Value)
    (hf : binFitsAt ct unsigned (Val.ofValue v)) (t : List U8) :
    binRead ct unsigned (binEncAt ct (Val.ofValue v) ++ t) = (some (binNormAt ct unsigned (Val.ofValue v)), t) := by
  sorry

/-- The text-row reader reads back a row of `NULL`s and byte strings. -/
theorem textRowRead_textEnc (vs : List Val) (hv : ∀ v ∈ vs, isTextVal v = true)
    (hs : ∀ s, Val.bytes s ∈ vs → s.length < 2 ^ 64) (t : List U8) :
    textRowRead vs.length ((vs.map textEnc).flatten ++ t) = (some vs, t) := by
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

/-- One step of the chunk reader keeps the state valid. -/
theorem chunkStep_valid (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) :
    (chunkStep st src dst max).2.1.Valid := by
  sorry

/-- The packet reader keeps the state valid. -/
theorem plainDecode_valid (seq : U8) (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) (comp : Option U8) :
    (plainDecode seq st src dst max comp).2.2.1.Valid := by
  sorry

/-- The fuel of `plainDecode` is enough: more fuel gives the same result. -/
theorem plainDecodeAux_fuel (f : Nat) (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8)
    (hf : src.length + 1 ≤ f) :
    plainDecodeAux f seq st src dst max comp = plainDecode seq st src dst max comp := by
  sorry

/-- The crate's packet reader reads back the chunks of a payload (the reference version of the codec round trip). -/
theorem plainDecode_frame (seq : U8) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max)
    (comp : Option U8) :
    plainDecode seq .idle (frame seq.val p ++ tail) [] max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p) := by
  sorry

/-- Resumption: on a strict prefix of the chunks the reader needs more input; continuing from the state it returns, on what it left followed by the rest of the chunks, reads the whole packet. -/
theorem plainDecode_resume (seq : U8) (p tail : List U8) (k : Nat) (hk : k < (frame seq.val p).length) (max : Nat)
    (hmax : p.length ≤ max) (comp : Option U8)
    (r : core.result.Result Bool proto.codec.error.PacketCodecError) (seq1 : U8) (st1 : ChunkState)
    (src1 dst1 : List U8)
    (h1 : plainDecode seq .idle ((frame seq.val p).take k) [] max comp = (r, seq1, st1, src1, dst1)) :
    r = .Ok false ∧
    plainDecode seq1 st1 (src1 ++ (frame seq.val p).drop k ++ tail) dst1 max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p) := by
  sorry

/-- Chunks with an unexpected sequence id (outside compressed mode) are out of sync; the expected id is kept. -/
theorem plainDecode_outOfSync (seq s : U8) (hs : s ≠ seq) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max) :
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).1 = .Err .PacketsOutOfSync ∧
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).2.1 = seq := by
  sorry

/-- The crate's column definition reader reads back the protocol layout (fields in range). -/
theorem colDefRead_colDefEnc (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEnc c ++ t) = (some c, t) := by
  sorry

/-- **The `Column` serialization bug, made precise**: what `MySerialize for Column` writes (`colDefEncCrate`) is read back by the crate's own reader without an error, but with `character_set` the low 16 bits of the column length and `column_length` the rest of the length plus the character set shifted by 16 bits. -/
theorem colDefRead_colDefEncCrate (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEncCrate c ++ t) =
      (some { c with charset := c.length % 2 ^ 16, length := c.length / 2 ^ 16 + 2 ^ 16 * c.charset }, t) := by
  sorry

/-- The OK packet reader reads back both forms of an OK packet (status with known flags, session state only when both flags are set). -/
theorem okPacketRead_okPacketEnc (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hl : b.info.length < 2 ^ 64 ∧ b.sessionStateInfo.length < 2 ^ 64) :
    okPacketRead .commonOk caps (okPacketEnc 0x00 caps compact b) = (some b.toPkt, []) := by
  sorry

/-- The ERR packet reader reads back a packet that fits the capabilities. -/
theorem errPacketRead_errPacketEnc (caps : Nat) (e : ErrPkt) (hc : errCompatible caps e)
    (hcode : ∀ code st msg, e = .error code st msg → code < 2 ^ 16 ∧ ∀ s, st = some s → s.length = 5)
    (hp : ∀ p, e = .progress p → p.stage < 256 ∧ p.maxStage < 256 ∧ p.info.length < 2 ^ 64) :
    errPacketRead caps (errPacketEnc e) = (some e, []) := by
  sorry

end Defs
