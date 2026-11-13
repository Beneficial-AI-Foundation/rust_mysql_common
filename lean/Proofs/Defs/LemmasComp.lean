import Defs

/-! Sanity lemmas about `Defs/Compression.lean` (recalled in `Specs/DefsComp.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace Defs

/-- A compressed-packet header has 7 bytes and reads back its fields (lengths below `2^24`). -/
theorem compHeaderRead_compHeader (cl seq pl : Nat) (hcl : cl < 2 ^ 24) (hpl : pl < 2 ^ 24) (t : List U8) :
    (compHeader cl seq pl).length = 7 ∧ compHeaderRead (compHeader cl seq pl ++ t) = (cl, byte seq, pl) := by
  sorry

/-- `chunksOf n` (for `n > 0`) cuts `bs` into non-empty pieces of at most `n` bytes that concatenate back to `bs`; all but the last have exactly `n` bytes, and there are `⌈|bs| / n⌉` of them. -/
theorem chunksOf_spec (n : Nat) (hn : 0 < n) (bs : List U8) :
    (chunksOf n bs).flatten = bs ∧ (chunksOf n bs).length = (bs.length + n - 1) / n ∧
    ∀ i c, (chunksOf n bs)[i]? = some c →
      c ≠ [] ∧ c.length ≤ n ∧ (i + 1 < (chunksOf n bs).length → c.length = n) := by
  sorry

/-- At compression level 0 the compressed form is unique: every piece is stored. -/
theorem compEncoding_level_zero (d0 : flate2.mem.Compress) (n seq : Nat) (plain out : List U8) :
    CompEncoding d0 0 n seq plain out ↔
      out = compPackets seq (chunksOf n plain) ((chunksOf n plain).map fun _ => none) := by
  sorry

/-- The crate's encoding is one of the streams the decoder accepts: its pieces are `chunksOf n plain`, each stored or deflated by flate2. Together with `chunksOf_spec` (pieces non-empty and at most `n` bytes) and `chunksOf_dropLast_length`, this gives `decode_compStream`'s hypotheses, so `PacketCodec.encode_decode_comp` follows from it. -/
theorem compEncoding_compStreamOf (d0 : flate2.mem.Compress) (level n seq : Nat) (plain out : List U8)
    (h : CompEncoding d0 level n seq plain out) : CompStreamOf seq (chunksOf n plain) out := by
  sorry

/-- All pieces of `chunksOf n bs` but the last hold fewer bytes than `bs` (for `n > 0` and non-empty `bs`): the stream ends in the last piece (`decode_compStream`'s `hlast`, with `rest = []`). -/
theorem chunksOf_dropLast_length (n : Nat) (hn : 0 < n) (bs : List U8) (hbs : bs ≠ []) :
    (chunksOf n bs).dropLast.flatten.length < bs.length := by
  sorry

/-- `CompState.of` is injective: the state keeps the decoder's variant (stored vs compressed, even for a caller-built `Compressed(n, 0)`) and all its fields. -/
theorem CompState.of_injective (a b : proto.codec.CompDecoder) (h : CompState.of a = CompState.of b) : a = b := by
  sorry

/-- A stored packet is 7 bytes longer than its piece, and a deflated one is shorter than that (by `Trusted.deflateResult_short`, its payload is non-empty and shorter than the piece). -/
theorem compPacket_length (level seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hc : CompChoice level chunk zo) :
    (compPacket seq chunk zo).length ≤ 7 + chunk.length ∧
    (∀ z, zo = some z → 7 < (compPacket seq chunk zo).length ∧ (compPacket seq chunk zo).length < 7 + chunk.length) := by
  sorry

/-- The reader reads back one packet written by the crate (stored, or deflated: by `Trusted.inflate_deflate`, with any inflate stream): the piece is appended, exactly the packet is consumed, idle again. -/
theorem compStep_compPacket (i : flate2.mem.Decompress) (seq : Nat) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (t dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    compStep (inflateList i) .idle (compPacket seq chunk zo ++ t) dst max =
      (.Ok (some (.Last (byte seq))), .idle, t, dst ++ chunk) := by
  sorry

/-- The reader keeps a valid state valid (for any inflate function). -/
theorem compStep_valid (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (st : CompState) (src dst : List U8) (max : Nat) (h : st.Valid) :
    (compStep inf st src dst max).2.1.Valid := by
  sorry

/-- On a strict prefix of a packet, the reader asks for more input and consumes nothing. -/
theorem compStep_prefix (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (seq : Nat) (chunk : List U8) (zo : Option (List U8)) (hz : ∀ z, zo = some z → Deflates chunk z)
    (k : Nat) (hk : k < (compPacket seq chunk zo).length) (dst : List U8) (max : Nat)
    (hmax : chunk.length ≤ Nat.min maxPayloadLen max) :
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).1 = .Ok none ∧
    (compStep inf .idle ((compPacket seq chunk zo).take k) dst max).2.2 =
      ((compPacket seq chunk zo).take k, dst) := by
  sorry

/-- `splitVersion` reads back `a.b.c` followed by anything that does not start with a digit, for parts in `0..=255` written in decimal. -/
theorem splitVersion_decimal (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (junk : List U8)
    (hj : ∀ d, junk.head? = some d → isDigit d = false) :
    splitVersion (decimalBytes a ++ byte 46 :: decimalBytes b ++ byte 46 :: decimalBytes c ++ junk) =
      some (byte a, byte b, byte c) := by
  sorry

/-- The crate's test cases: `"1.2.3"`, `"10.20.30foo"`, `"100.200.300foo"` (a part above 255: none), and two quirks: a sign is accepted in the first two parts, and fewer than two dots give none. -/
theorem splitVersion_examples :
    splitVersion (utf8 "1.2.3") = some (byte 1, byte 2, byte 3) ∧
    splitVersion (utf8 "10.20.30foo") = some (byte 10, byte 20, byte 30) ∧
    splitVersion (utf8 "8.0.36-log") = some (byte 8, byte 0, byte 36) ∧
    splitVersion (utf8 "100.200.300foo") = none ∧
    splitVersion (utf8 "+5.-0.7") = some (byte 5, byte 0, byte 7) ∧
    splitVersion (utf8 "8.0") = none ∧
    splitVersion (utf8 "8.0.x") = none := by
  sorry

end Defs
