import Defs.Bytes

/-!
# Packet framing

From the protocol, "MySQL Packets"
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_packets.html>):
a payload is sent as one or more chunks, each a 3-byte little-endian payload length, a 1-byte
sequence id, then that many payload bytes. A payload of `2^24 - 1` bytes or more is split into
chunks of `2^24 - 1` bytes; the last chunk is shorter, and is empty if the length is a multiple of
`2^24 - 1` (so an empty payload is one empty chunk). The sequence id goes up by one per chunk,
wrapping around after 255.

The crate's incremental reader (`ChunkDecoder`, `PlainPacketCodec::decode`) is described by
`chunkStep` and `plainDecode`: they spell out how much input each call consumes and what state it
leaves, which the protocol page does not prescribe.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- `MAX_PAYLOAD_LEN`: the largest payload of one chunk, `2^24 - 1`. -/
def maxPayloadLen : Nat := 2 ^ 24 - 1

/-- The chunks of the payload `p`, the first with sequence id `seq` (mod 256). -/
def frame (seq : Nat) (p : List U8) : List U8 :=
  if p.length < maxPayloadLen then leBytes 3 p.length ++ byte seq :: p
  else leBytes 3 maxPayloadLen ++ byte seq :: p.take maxPayloadLen ++ frame (seq + 1) (p.drop maxPayloadLen)
termination_by p.length
decreasing_by simp [maxPayloadLen] at *; omega

/-- The number of chunks `frame` uses for a payload of `n` bytes (so the sequence id after
    sending it is `seq + frameCount n`, mod 256). -/
def frameCount (n : Nat) : Nat := n / maxPayloadLen + 1

/-! ## The crate's incremental chunk reader -/

/-- The state of the crate's chunk reader (`ChunkDecoder`): idle (waiting for a chunk header), or
    a header with sequence id `seq` and payload length `needed > 0` seen but not yet consumed,
    waiting for the payload. -/
inductive ChunkState where
  | idle
  | chunk (seq : U8) (needed : Nat)
deriving DecidableEq

/-- The `ChunkState` of a `ChunkDecoder`. -/
def ChunkState.of : proto.codec.ChunkDecoder → ChunkState
  | .Idle => .idle
  | .Chunk seq needed => .chunk seq needed.val

/-- A `ChunkDecoder` state that the decoder can be in: a pending chunk has a length between 1 and
    `2^24 - 1`. `needed ≠ 0` is a type invariant (`needed` is a `NonZeroUsize`, whose field is
    private); `needed < 2^24` holds for every state the decoder produces (the length comes from a
    3-byte field, `chunkStep_valid`) but is an **assumption** on a state built by a caller, since
    the fields of `ChunkDecoder::Chunk` are public. -/
def ChunkState.Valid : ChunkState → Prop
  | .idle => True
  | .chunk _ needed => 0 < needed ∧ needed < 2 ^ 24

/-- The sequence id of a `ChunkInfo`. -/
def chunkInfoSeq : proto.codec.ChunkInfo → U8
  | .Middle s => s
  | .Last s => s

/-- One call of the crate's chunk reader on the input `src`, appending to `dst`, with packet size
    limit `max`. The result is `Ok none` (more input needed), `Ok (some info)` (a chunk was read)
    or `Err PacketTooLarge`, with the new state, input and output.
    * Idle, fewer than 4 bytes: more input needed; nothing consumed.
    * Idle, a header of length 0: an empty last chunk; the header is consumed.
    * Idle, a header of length `len > 0` with `dst.length + len > max`: `PacketTooLarge`; nothing
      consumed. (An empty chunk is never checked against `max`.)
    * Idle, a header of length `len > 0` otherwise: as the pending state `chunk seq len`.
    * Pending `chunk seq len`: if the header and the whole payload are there, both are consumed and
      the payload appended to `dst`; the chunk is `Middle` iff the new `dst.length` is a multiple
      of `2^24 - 1` (the crate's test; this means "a full chunk, more follow" only if `dst` held
      nothing but earlier chunks of the same packet) and `Last` otherwise. If not, more input is
      needed: nothing is consumed, and the state is `chunk seq len` (the header stays in `src`
      until the payload is complete). -/
def chunkStep (st : ChunkState) (src dst : List U8) (max : Nat) :
    core.result.Result (Option proto.codec.ChunkInfo) proto.codec.error.PacketCodecError
      × ChunkState × List U8 × List U8 :=
  let body (seq : U8) (len : Nat) :=
    if 4 + len ≤ src.length then
      let dst' := dst ++ (src.drop 4).take len
      (.Ok (some (if dst'.length % maxPayloadLen = 0 then .Middle seq else .Last seq)), ChunkState.idle,
        src.drop (4 + len), dst')
    else (.Ok none, ChunkState.chunk seq len, src, dst)
  match st with
  | .idle =>
    if src.length < 4 then (.Ok none, .idle, src, dst)
    else
      let len := leNat (src.take 3)
      let seq := src.getD 3 (byte 0)
      if len = 0 then (.Ok (some (.Last seq)), .idle, src.drop 4, dst)
      else if max < dst.length + len then (.Err .PacketTooLarge, .idle, src, dst)
      else body seq len
  | .chunk seq len => body seq len

/-- `plainDecode` with an explicit bound on the number of chunks read (see `plainDecode`). -/
def plainDecodeAux : Nat → U8 → ChunkState → List U8 → List U8 → Nat → Option U8 →
    core.result.Result Bool proto.codec.error.PacketCodecError × U8 × ChunkState × List U8 × List U8
  | 0, seq, st, src, dst, _, _ => (.Ok false, seq, st, src, dst)
  | fuel + 1, seq, st, src, dst, max, comp =>
    match chunkStep st src dst max with
    | (.Err e, st', src', dst') => (.Err e, seq, st', src', dst')
    | (.Ok none, st', src', dst') => (.Ok false, seq, st', src', dst')
    | (.Ok (some info), st', src', dst') =>
      let s := chunkInfoSeq info
      if seq ≠ s ∧ comp ≠ some s then (.Err .PacketsOutOfSync, seq, st', src', dst')
      else
        let seq' := byte (s.val + 1)
        match info with
        | .Last _ => (.Ok true, seq', st', src', dst')
        | .Middle _ =>
          if src' = [] then (.Ok false, seq', st', src', dst')
          else plainDecodeAux fuel seq' st' src' dst' max comp

/-- The crate's packet reader (`PlainPacketCodec::decode`) with expected sequence id `seq`, chunk
    reader state `st`, input `src`, output `dst`, size limit `max` and (in compressed mode) the
    sequence id `comp` of the last compressed packet. It reads chunks with `chunkStep` until the
    last chunk of a packet (`Ok true`), more input is needed (`Ok false`), or an error:
    * a chunk whose sequence id is neither `seq` nor `comp`: `PacketsOutOfSync` (the chunk has been
      consumed and appended to `dst`);
    * otherwise the expected sequence id becomes the chunk's plus one (mod 256).
    The result is the outcome, the new expected sequence id, the new reader state, input and
    output. (A recursive call follows only a `Middle` chunk, which consumed at least 4 bytes
    (`4 + len ≥ 5` from a valid state: zero-length chunks are `Last`). So `src.length + 1` chunk reads always suffice and the bound is
    never reached; see `plainDecodeAux_fuel`.) -/
def plainDecode (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8) :
    core.result.Result Bool proto.codec.error.PacketCodecError × U8 × ChunkState × List U8 × List U8 :=
  plainDecodeAux (src.length + 1) seq st src dst max comp

end Defs
