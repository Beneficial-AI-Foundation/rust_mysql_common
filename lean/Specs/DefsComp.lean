import Proofs.Defs.LemmasComp

/-!
# Facts about the compression and version definitions (`lean/Defs/Compression.lean`)

Properties of the definitions used by the compressed-codec statements in `Specs/Proto/Codec.lean`
and by `split_version` in `Specs/Misc.lean`. A signer should read them. They check that:
* a header reads back its fields;
* `chunksOf` cuts a stream as described;
* level 0 forces stored packets;
* the crate's encoding is a stream the decoder accepts (`compEncoding_compStreamOf`);
* `CompState.of` is injective;
* the packet reader `compStep` reads back what the crate writes (with `Trusted.inflate_deflate`),
  waits on a prefix and keeps valid states valid;
* `splitVersion` behaves as the crate's tests expect, including its quirks.
Proofs: `Proofs/Defs/LemmasComp.lean`.

**Trusted axioms.** The statements about deflated packets (`compPacket_length`,
`compStep_compPacket`) rest on `Trusted.deflateResult_short` and `Trusted.inflate_deflate`; the
others are plain Lean.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- A compressed-packet header has 7 bytes and reads back its fields (lengths below `2^24`). -/
recall compHeaderRead_compHeader (cl seq pl : Nat) (hcl : cl < 2 ^ 24) (hpl : pl < 2 ^ 24) (t : List U8) :
    (compHeader cl seq pl).length = 7 ∧ compHeaderRead (compHeader cl seq pl ++ t) = (cl, byte seq, pl)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compHeaderRead_compHeader`
/-- `chunksOf n` (for `n > 0`) cuts `bs` into non-empty pieces of at most `n` bytes that concatenate back to `bs`; all but the last have exactly `n` bytes, and there are `⌈|bs| / n⌉` of them. -/
recall chunksOf_spec (n : Nat) (hn : 0 < n) (bs : List U8) :
    (chunksOf n bs).flatten = bs ∧ (chunksOf n bs).length = (bs.length + n - 1) / n ∧
    ∀ i c, (chunksOf n bs)[i]? = some c →
      c ≠ [] ∧ c.length ≤ n ∧ (i + 1 < (chunksOf n bs).length → c.length = n)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.chunksOf_spec`
/-- At compression level 0 the compressed form is unique: every piece is stored. -/
recall compEncoding_level_zero (n seq : Nat) (plain out : List U8) :
    CompEncoding 0 n seq plain out ↔
      out = compPackets seq (chunksOf n plain) ((chunksOf n plain).map fun _ => none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compEncoding_level_zero`
/-- The crate's encoding is one of the streams the decoder accepts: with `n > 0`, its pieces are the non-empty `chunksOf n plain`, each stored or deflated by flate2 (so `PacketCodec.encode_decode_comp` follows from `CompPacketCodec.decode_compStream`). -/
recall compEncoding_compStreamOf (level n seq : Nat) (hn : 0 < n) (plain out : List U8)
    (h : CompEncoding level n seq plain out) : CompStreamOf seq (chunksOf n plain) out

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compEncoding_compStreamOf`
/-- `CompState.of` is injective: the state keeps the decoder's variant (stored vs compressed, even for a caller-built `Compressed(n, 0)`) and all its fields. -/
recall CompState.of_injective (a b : proto.codec.CompDecoder) (h : CompState.of a = CompState.of b) : a = b

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.CompState.of_injective`
/-- A stored packet is 7 bytes longer than its piece, and a deflated one is shorter than that (by `Trusted.deflateResult_short`, its payload is non-empty and shorter than the piece). -/
recall compPacket_length (level seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hc : CompChoice level chunk zo) :
    (compPacket seq chunk zo).length ≤ 7 + chunk.length ∧
    (∀ z, zo = some z → 7 < (compPacket seq chunk zo).length ∧ (compPacket seq chunk zo).length < 7 + chunk.length)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compPacket_length`
/-- The reader reads back one packet written by the crate (stored, or deflated: by `Trusted.inflate_deflate`, with any inflate stream): the piece is appended, exactly the packet is consumed, idle again. -/
recall compStep_compPacket (i : flate2.mem.Decompress) (seq : Nat) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (t dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    compStep (inflateList i) .idle (compPacket seq chunk zo ++ t) dst max =
      (.Ok (some (.Last (byte seq))), .idle, t, dst ++ chunk)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compStep_compPacket`
/-- The reader keeps a valid state valid (for any inflate function). -/
recall compStep_valid (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (st : CompState) (src dst : List U8) (max : Nat) (h : st.Valid) :
    (compStep inf st src dst max).2.1.Valid

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compStep_valid`
/-- On a strict prefix of a packet, the reader asks for more input and consumes nothing. -/
recall compStep_prefix (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hz : ∀ z, zo = some z → Deflates chunk z)
    (k : Nat) (hk : k < (compPacket seq chunk zo).length) (dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).1 = .Ok none ∧
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).2.2 =
      ((compPacket seq chunk zo).take k, dst)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.compStep_prefix`
/-- `splitVersion` reads back `a.b.c` followed by anything that does not start with a digit, for parts in `0..=255` written in decimal. -/
recall splitVersion_decimal (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (junk : List U8)
    (hj : ∀ d, junk.head? = some d → isDigit d = false) :
    splitVersion (decimalBytes a ++ byte 46 :: decimalBytes b ++ byte 46 :: decimalBytes c ++ junk) =
      some (byte a, byte b, byte c)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.splitVersion_decimal`
/-- The crate's test cases: `"1.2.3"`, `"10.20.30foo"`, `"100.200.300foo"` (a part above 255: none), and two quirks: a sign is accepted in the first two parts, and fewer than two dots give none. -/
recall splitVersion_examples :
    splitVersion (utf8 "1.2.3") = some (byte 1, byte 2, byte 3) ∧
    splitVersion (utf8 "10.20.30foo") = some (byte 10, byte 20, byte 30) ∧
    splitVersion (utf8 "8.0.36-log") = some (byte 8, byte 0, byte 36) ∧
    splitVersion (utf8 "100.200.300foo") = none ∧
    splitVersion (utf8 "+5.-0.7") = some (byte 5, byte 0, byte 7) ∧
    splitVersion (utf8 "8.0") = none ∧
    splitVersion (utf8 "8.0.x") = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.splitVersion_examples`
end Defs
