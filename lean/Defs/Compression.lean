import Defs.Framing
import Defs.Convert

/-!
# Compressed packets, and server version strings

From the protocol, "Compression"
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_compression.html>) and
"Compressed Packet"
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_compression_packet.html>):
once compression is on, the byte stream of plain packets (their chunks as `frame` writes them,
`Defs/Framing.lean`) is cut into pieces, and each piece is sent as one compressed packet:

* a 7-byte header: the 3-byte little-endian length of the compressed payload, a 1-byte
  compressed sequence id (its own counter, going up by one per compressed packet and wrapping
  after 255), and the 3-byte little-endian length of the payload before compression;
* then the payload: the piece deflated (zlib), or, if the uncompressed length field is 0, the
  piece itself, stored as is.

A sender may store any piece (the server, for example, only compresses payloads of at least
`MIN_COMPRESS_LENGTH` = 50 bytes, and sends a piece uncompressed when deflating does not make it
shorter); the crate's threshold is 512 bytes (`minCompressLength`). A piece is at most
`2^24 - 1` bytes (the length field has 3 bytes); the crate cuts the stream into pieces of
`min(2^24 - 1, max_allowed_packet)` bytes.

zlib itself is not defined here: what a deflated payload is comes from flate2 through the
`Trusted` axioms of `MysqlCommon/FunsExternal.lean` (`Deflates`, `inflateList`), which only say
what deflate and inflate do when they succeed.

The incremental reader of compressed packets (`CompDecoder`) is described by `compStep`, in the
style of `chunkStep`: how much input each call consumes and what state it leaves, which the
protocol page does not prescribe.

**Version strings.** `splitVersion` reads the `X.Y.Z` prefix of a server version string such as
`8.0.36-log` (the `server_version` of the initial handshake).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## The compressed packet format -/

/-- The crate's `MIN_COMPRESS_LENGTH`: a piece shorter than 512 bytes is always stored, never
    deflated. (The protocol allows any piece to be stored; the server's own threshold is 50.) -/
def minCompressLength : Nat := 512

/-- A compressed-packet header: compressed length `compLen` (3 bytes LE), sequence id `seq`
    (mod 256), uncompressed length `plainLen` (3 bytes LE; 0 = the payload is stored). -/
def compHeader (compLen seq plainLen : Nat) : List U8 :=
  leBytes 3 compLen ++ byte seq :: leBytes 3 plainLen

/-- The fields `(compLen, seq, plainLen)` of the header at the start of `bs` (at least 7 bytes). -/
def compHeaderRead (bs : List U8) : Nat × U8 × Nat :=
  (leNat (bs.take 3), bs.getD 3 (byte 0), leNat ((bs.drop 4).take 3))

/-- The compressed packet with sequence id `seq` carrying the piece `chunk`: stored
    (`none`: uncompressed length 0, then the piece) or deflated to `z` (`some z`: compressed
    length `z.length`, uncompressed length `chunk.length`, then `z`). -/
def compPacket (seq : Nat) (chunk : List U8) : Option (List U8) → List U8
  | none => compHeader chunk.length seq 0 ++ chunk
  | some z => compHeader z.length seq chunk.length ++ z

/-- The compressed packets carrying the pieces `chunks`, the first with sequence id `seq` and
    each next one with the next id, the `i`-th stored or deflated as `zs[i]` says. -/
def compPackets (seq : Nat) : List (List U8) → List (Option (List U8)) → List U8
  | c :: cs, z :: zs => compPacket seq c z ++ compPackets (seq + 1) cs zs
  | _, _ => []

/-- `bs` cut into consecutive pieces of `n` bytes, the last one shorter (and no empty piece:
    `[]` for an empty `bs`). For `n = 0`, `[]` (the crate panics instead, see the specs). -/
def chunksOf (n : Nat) (bs : List U8) : List (List U8) :=
  if n = 0 then []
  else if bs = [] then []
  else bs.take n :: chunksOf n (bs.drop n)
termination_by bs.length
decreasing_by
  simp only [List.length_drop]
  have : bs.length ≠ 0 := by simpa using ‹¬bs = []›
  omega

/-- `z` is what flate2 produced when deflating `chunk` successfully, with some deflate stream
    (`Trusted.deflateResult`: a complete zlib stream, shorter than `chunk`). -/
def Deflates (chunk z : List U8) : Prop :=
  ∃ (d : flate2.mem.Compress) (c : Slice U8) (v : alloc.vec.Vec U8),
    c.val = chunk ∧ v.val = z ∧ Trusted.deflateResult d c = .Ok (some v)

/-- How a piece `chunk` may be carried at compression level `level` (a necessary condition):
    stored always; deflated to `z` only when compression is on (`level ≠ 0`), the piece has at
    least `minCompressLength` bytes, and `z` is a successful deflate of it. -/
def CompChoice (level : Nat) (chunk : List U8) : Option (List U8) → Prop
  | none => True
  | some z => level ≠ 0 ∧ minCompressLength ≤ chunk.length ∧ Deflates chunk z

/-- `d'` is a deflate stream reachable from `d` by deflating zero or more slices
    (`Trusted.deflateState`): the streams an encoder that starts with `d` can be using. -/
inductive DeflateReach : flate2.mem.Compress → flate2.mem.Compress → Prop
  | refl (d : flate2.mem.Compress) : DeflateReach d d
  | step (d d' : flate2.mem.Compress) (c : Slice U8) :
      DeflateReach (Trusted.deflateState d c) d' → DeflateReach d d'

/-- How the crate's encoder, starting with the deflate stream `d0`, carries the piece `chunk` at
    level `level`: as `CompChoice`, and stored only if it has to be. That is the case when
    compression is off, when the piece is shorter than `minCompressLength`, or when deflating it
    succeeded without making it shorter (flate2 gave `Ok None` with a stream reachable from
    `d0`, i.e. the one the encoder holds then). -/
def EncChoice (d0 : flate2.mem.Compress) (level : Nat) (chunk : List U8) (zo : Option (List U8)) : Prop :=
  CompChoice level chunk zo ∧
  (zo = none → level = 0 ∨ chunk.length < minCompressLength ∨
    ∃ (d : flate2.mem.Compress) (c : Slice U8),
      DeflateReach d0 d ∧ c.val = chunk ∧ Trusted.deflateResult d c = .Ok none)

/-- `out` is a sequence of compressed packets carrying the pieces `chunks` in order from sequence
    id `seq`, as the crate's encoder starting with stream `d0` writes them (`EncChoice d0 level`). -/
def CompPacketsOf (d0 : flate2.mem.Compress) (level seq : Nat) (chunks : List (List U8))
    (out : List U8) : Prop :=
  ∃ zs : List (Option (List U8)), List.Forall₂ (EncChoice d0 level) chunks zs ∧
    out = compPackets seq chunks zs

/-- `out` is the crate's compressed form of the byte stream `plain`, by an encoder starting with
    stream `d0`: cut into pieces of `n` bytes (`chunksOf`), from sequence id `seq`, at compression
    level `level`. At level 0 it is unique: every piece is stored (`compEncoding_level_zero`). -/
def CompEncoding (d0 : flate2.mem.Compress) (level n seq : Nat) (plain out : List U8) : Prop :=
  CompPacketsOf d0 level seq (chunksOf n plain) out

/-- `out` is any sequence of compressed packets carrying the pieces `pieces` in order, from
    sequence id `seq`, each stored or deflated by flate2 (`Deflates`). Any cut and any choice
    are allowed, so this is what the decode statements accept. (A deflated piece is covered only
    when it is flate2/miniz_oxide's own output, the limit of `Trusted.inflate_deflate`; another
    zlib implementation's stream is not.) -/
def CompStreamOf (seq : Nat) (pieces : List (List U8)) (out : List U8) : Prop :=
  ∃ zs : List (Option (List U8)),
    List.Forall₂ (fun c zo => ∀ z, zo = some z → Deflates c z) pieces zs ∧
    out = compPackets seq pieces zs

/-- The size of the pieces the crate cuts the stream into, for a given `max_allowed_packet`. -/
def compChunkSize (max : Nat) : Nat := Nat.min maxPayloadLen max

/-- inflate of `z` into `n` bytes with the stream `i`, as a list function: flate2's result
    (`Trusted.inflateResult`, which is only specified on success) on the slice holding `z`.
    (Both side conditions hold wherever the specs use it: `z` is part of a buffer, and `n < 2^24`
    comes from a 3-byte field. Outside them the value `.Ok []` is arbitrary.) -/
noncomputable def inflateList (i : flate2.mem.Decompress) (z : List U8) (n : Nat) :
    core.result.Result (List U8) core.io.error.Error :=
  if h : z.length ≤ Usize.max then
    match Trusted.inflateResult i (Slice.from z h) ⟨BitVec.ofNat _ n⟩ with
    | .Ok v => .Ok v.val
    | .Err e => .Err e
  else .Ok []

/-! ## The crate's incremental compressed-packet reader -/

/-- The state of the crate's compressed-packet reader (`CompDecoder`). It is idle (waiting for a
    header), or a header has been seen but not yet consumed and the reader waits for the payload.
    A pending header has sequence id `seq` and compressed length `compLen`. Its `plainLen` is
    `none` for a stored payload (`CompData::Uncompressed`) and `some p` for a payload to inflate
    to `p` bytes (`CompData::Compressed`). The variant is kept apart from the length because a
    caller can build `Compressed(n, 0)` (see `CompState.Valid`), and the crate inflates such a
    payload rather than storing it. -/
inductive CompState where
  | idle
  | packet (seq : U8) (compLen : Nat) (plainLen : Option Nat)
deriving DecidableEq

/-- The `CompState` of a `CompDecoder` (injective: `CompState.of_injective`). -/
def CompState.of : proto.codec.CompDecoder → CompState
  | .Idle => .idle
  | .Packet seq (.Uncompressed n) => .packet seq n.val none
  | .Packet seq (.Compressed n p) => .packet seq n.val (some p.val)

/-- A state the reader can produce. In a pending header, the compressed length is non-zero and
    below `2^24`, and a compressed payload's length is non-zero and below `2^24`. (The 3-byte
    fields bound the lengths; `CompData::new` gives the non-zero lengths.) In Rust the non-zero
    lengths are also type invariants (`NonZeroUsize`). The translation's `NonZeroUsize` is a plain
    `usize`, and the fields of `CompDecoder::Packet` are public, so other states can be built in
    Lean; the decode specs only ask for `compStepFits`. -/
def CompState.Valid : CompState → Prop
  | .idle => True
  | .packet _ cl pl => 0 < cl ∧ cl < 2 ^ 24 ∧ ∀ p, pl = some p → 0 < p ∧ p < 2 ^ 24

/-- One call of the crate's compressed-packet reader on input `src`, appending the packet's
    plain bytes to `dst`, with size limit `max`, inflating with `inf` (see `inflateList`).
    * Idle, fewer than 7 bytes: more input needed (`Ok none`); nothing consumed.
    * Idle, a header with `max < max(compLen, plainLen)`: `PacketTooLarge`; nothing consumed.
    * Idle, a header with `compLen = 0`: if `plainLen = 0`, an empty packet (`Ok (Last seq)`),
      the header consumed; otherwise `BadCompressedPacketHeader`, nothing consumed.
    * Idle, another header: as the pending state (`plainLen = 0`: stored).
    * Pending, with the header and the whole payload there:
      - a stored payload is appended to `dst`;
      - a compressed one is inflated to its length and appended;
      - both are consumed, and the result is `Ok (Last seq)`, idle.
      - If inflating fails with `e`: `Err (Io e)`. The crate has then consumed the 7 header
        bytes but stays in the pending state (see the quirk in `Specs/Proto/Codec.lean`).
    * Pending, with the payload not all there: more input needed, nothing consumed, the pending
      state kept. -/
def compStep (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (st : CompState) (src dst : List U8) (max : Nat) :
    core.result.Result (Option proto.codec.ChunkInfo) proto.codec.error.PacketCodecError
      × CompState × List U8 × List U8 :=
  let body (seq : U8) (cl : Nat) (pl : Option Nat) :=
    if 7 + cl ≤ src.length then
      let z := (src.drop 7).take cl
      match pl with
      | none => (.Ok (some (.Last seq)), CompState.idle, src.drop (7 + cl), dst ++ z)
      | some p =>
        match inf z p with
        | .Ok v => (.Ok (some (.Last seq)), CompState.idle, src.drop (7 + cl), dst ++ v)
        | .Err e => (.Err (.Io e), CompState.packet seq cl pl, src.drop 7, dst)
    else (.Ok none, CompState.packet seq cl pl, src, dst)
  match st with
  | .idle =>
    if src.length < 7 then (.Ok none, .idle, src, dst)
    else
      let (cl, seq, pl) := compHeaderRead src
      if max < Nat.max cl pl then (.Err .PacketTooLarge, .idle, src, dst)
      else if cl = 0 then
        if pl = 0 then (.Ok (some (.Last seq)), .idle, src.drop 7, dst)
        else (.Err .BadCompressedPacketHeader, .idle, src, dst)
      else body seq cl (if pl = 0 then none else some pl)
  | .packet seq cl pl => body seq cl pl

/-- The lengths one call of the compressed-packet reader computes fit in a `usize` (stronger
    than necessary, for simplicity). Idle: `dst` has room for `2^24` more bytes (a payload is
    below `2^24`). Pending: `7 + compLen` fits, and `dst` has room for either length. -/
def compStepFits (st : CompState) (dst : List U8) : Prop :=
  match st with
  | .idle => dst.length + 2 ^ 24 ≤ Usize.max
  | .packet _ cl pl =>
    7 + cl ≤ Usize.max ∧ dst.length + cl ≤ Usize.max ∧ dst.length + pl.getD 0 ≤ Usize.max

/-! ## Server version strings (the crate's reading)

`split_version` has no protocol definition: the handshake's `server_version` is free text. These
definitions describe the crate's reading of it. -/

/-- One numeric part of a version, as the crate reads it with `btoi`: the bytes are an ASCII
    integer (`asciiInt`) with value in `0..=255`. `asciiInt` accepts an optional `+` or `-` sign
    before the digits; that is a btoi quirk, not part of any version format. -/
def versionPart (bs : List U8) : Option U8 :=
  (asciiInt bs).bind fun v => if 0 ≤ v ∧ v < 256 then some (byte v.toNat) else none

/-- The crate's reading of a version string `bs` as `(major, minor, patch)`.
    * The parts before the first and the second `.` (46) are the major and minor version.
    * The patch version is the longest run of ASCII digits right after the second `.`; anything
      after it, such as `-log` or a fourth part, is ignored.
    * `none` if there are fewer than two `.`, or a part is not a number in `0..=255`. -/
def splitVersion (bs : List U8) : Option (U8 × U8 × U8) :=
  let notDot : U8 → Bool := fun c => c.val ≠ 46
  match bs.dropWhile notDot with
  | [] => none
  | _ :: r0 =>
    match r0.dropWhile notDot with
    | [] => none
    | _ :: r1 => do
      let a ← versionPart (bs.takeWhile notDot)
      let b ← versionPart (r0.takeWhile notDot)
      let c ← versionPart (r1.takeWhile isDigit)
      some (a, b, c)

end Defs
