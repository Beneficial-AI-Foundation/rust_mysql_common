import Proofs.Defs.LemmasCF

/-!
# Facts about the stage c–f definitions (`lean/Defs/`)

Pure-Lean properties of the definitions used by `Specs/Constants.lean`, `Specs/Row.lean`,
`Specs/Packets.lean` and `Specs/Proto/Codec.lean`. A signer should read them: they check that the
readers invert the encoders, that the encoders have the shapes the protocol pages describe, that
the codec's reader can be resumed and keeps its state valid, and they pin down the `Column`
serialization bug (`colDefRead_colDefEncCrate`). Proofs: `Proofs/Defs/LemmasCF.lean`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- Every column type's code is a byte, and decodes back to it. -/
recall columnTypeOfCode_columnTypeCode (ct : constants.ColumnType) :
    columnTypeCode ct < 256 ∧ columnTypeOfCode (columnTypeCode ct) = some ct

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.columnTypeOfCode_columnTypeCode`

/-- A NULL bitmap has `nullBitmapLen` bytes, and its bit for field `i` is `nulls[i]`. -/
recall nullBitmap_spec (off : Nat) (nulls : List Bool) :
    (nullBitmap off nulls).length = nullBitmapLen off nulls.length ∧
    ∀ i, bitmapBit off (nullBitmap off nulls) i = nulls.getD i false

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.nullBitmap_spec`

/-- The binary value decoder reads back a `Value` encoded at its column's type (`binEncAt`), when it fits the column (`binFitsAt`), up to `binNormAt`. -/
recall binRead_binEncAt (ct : constants.ColumnType) (unsigned : Bool) (v : value.Value)
    (hf : binFitsAt ct unsigned (Val.ofValue v)) (t : List U8) :
    binRead ct unsigned (binEncAt ct (Val.ofValue v) ++ t) = (some (binNormAt ct unsigned (Val.ofValue v)), t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.binRead_binEncAt`

/-- The text-row reader reads back a row of `NULL`s and byte strings. -/
recall textRowRead_textEnc (vs : List Val) (hv : ∀ v ∈ vs, isTextVal v = true)
    (hs : ∀ s, Val.bytes s ∈ vs → s.length < 2 ^ 64) (t : List U8) :
    textRowRead vs.length ((vs.map textEnc).flatten ++ t) = (some vs, t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.textRowRead_textEnc`

/-- An empty payload is one empty chunk. -/
recall frame_nil (seq : Nat) : frame seq [] = [byte 0, byte 0, byte 0, byte seq]

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.frame_nil`

/-- A payload shorter than `2^24 - 1` is one chunk. -/
recall frame_short (seq : Nat) (p : List U8) (h : p.length < maxPayloadLen) :
    frame seq p = leBytes 3 p.length ++ byte seq :: p

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.frame_short`

/-- The chunks of a payload: its bytes plus a 4-byte header per chunk. -/
recall frame_length (seq : Nat) (p : List U8) :
    (frame seq p).length = p.length + 4 * frameCount p.length

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.frame_length`

/-- One step of the chunk reader keeps the state valid. -/
recall chunkStep_valid (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) :
    (chunkStep st src dst max).2.1.Valid

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.chunkStep_valid`

/-- The packet reader keeps the state valid. -/
recall plainDecode_valid (seq : U8) (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) (comp : Option U8) :
    (plainDecode seq st src dst max comp).2.2.1.Valid

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.plainDecode_valid`

/-- The fuel of `plainDecode` is enough: more fuel gives the same result. -/
recall plainDecodeAux_fuel (f : Nat) (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8)
    (hf : src.length + 1 ≤ f) :
    plainDecodeAux f seq st src dst max comp = plainDecode seq st src dst max comp

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.plainDecodeAux_fuel`

/-- The crate's packet reader reads back the chunks of a payload (the reference version of the codec round trip). -/
recall plainDecode_frame (seq : U8) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max)
    (comp : Option U8) :
    plainDecode seq .idle (frame seq.val p ++ tail) [] max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.plainDecode_frame`

/-- Resumption: on a strict prefix of the chunks the reader needs more input; continuing from the state it returns, on what it left followed by the rest of the chunks, reads the whole packet. -/
recall plainDecode_resume (seq : U8) (p tail : List U8) (k : Nat) (hk : k < (frame seq.val p).length) (max : Nat)
    (hmax : p.length ≤ max) (comp : Option U8)
    (r : core.result.Result Bool proto.codec.error.PacketCodecError) (seq1 : U8) (st1 : ChunkState)
    (src1 dst1 : List U8)
    (h1 : plainDecode seq .idle ((frame seq.val p).take k) [] max comp = (r, seq1, st1, src1, dst1)) :
    r = .Ok false ∧
    plainDecode seq1 st1 (src1 ++ (frame seq.val p).drop k ++ tail) dst1 max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.plainDecode_resume`

/-- Chunks with an unexpected sequence id (outside compressed mode) are out of sync; the expected id is kept. -/
recall plainDecode_outOfSync (seq s : U8) (hs : s ≠ seq) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max) :
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).1 = .Err .PacketsOutOfSync ∧
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).2.1 = seq

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.plainDecode_outOfSync`

/-- The crate's column definition reader reads back the protocol layout (fields in range). -/
recall colDefRead_colDefEnc (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEnc c ++ t) = (some c, t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.colDefRead_colDefEnc`

/-- **The `Column` serialization bug, made precise**: what `MySerialize for Column` writes (`colDefEncCrate`) is read back by the crate's own reader without an error, but with `character_set` the low 16 bits of the column length and `column_length` the rest of the length plus the character set shifted by 16 bits. -/
recall colDefRead_colDefEncCrate (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEncCrate c ++ t) =
      (some { c with charset := c.length % 2 ^ 16, length := c.length / 2 ^ 16 + 2 ^ 16 * c.charset }, t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.colDefRead_colDefEncCrate`

/-- The OK packet reader reads back both forms of an OK packet (status with known flags, session state only when both flags are set). -/
recall okPacketRead_okPacketEnc (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hl : b.info.length < 2 ^ 64 ∧ b.sessionStateInfo.length < 2 ^ 64) :
    okPacketRead .commonOk caps (okPacketEnc 0x00 caps compact b) = (some b.toPkt, [])

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.okPacketRead_okPacketEnc`

/-- The ERR packet reader reads back a packet that fits the capabilities. -/
recall errPacketRead_errPacketEnc (caps : Nat) (e : ErrPkt) (hc : errCompatible caps e)
    (hcode : ∀ code st msg, e = .error code st msg → code < 2 ^ 16 ∧ ∀ s, st = some s → s.length = 5)
    (hp : ∀ p, e = .progress p → p.stage < 256 ∧ p.maxStage < 256 ∧ p.info.length < 2 ^ 64) :
    errPacketRead caps (errPacketEnc e) = (some e, [])

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.errPacketRead_errPacketEnc`

end Defs
