import Defs.CmdPackets

/-!
# Replication commands (`COM_REGISTER_SLAVE`, `COM_TABLE_DUMP`, `COM_BINLOG_DUMP`,
  `COM_BINLOG_DUMP_GTID`, the semi-sync ACK)

From the protocol pages:

* `COM_REGISTER_SLAVE`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_register_slave.html>):
  `0x15`, `server_id` (4), `hostname`, `user`, `password` (each a 1-byte length and the bytes),
  `port` (2), `replication_rank` (4), `master_id` (4).
* `COM_TABLE_DUMP` (deprecated, `0x13`): the database and the table name, each a 1-byte length
  and the bytes.
* `COM_BINLOG_DUMP`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_binlog_dump.html>):
  `0x12`, `binlog_pos` (4), `flags` (2: `BINLOG_DUMP_NON_BLOCK` = 1), `server_id` (4),
  `binlog_filename` (the rest of the packet).
* `COM_BINLOG_DUMP_GTID`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_binlog_dump_gtid.html>):
  `0x1E`, `flags` (2: `BINLOG_DUMP_NON_BLOCK` = 1, `BINLOG_THROUGH_POSITION` = 2,
  `BINLOG_THROUGH_GTID` = 4), `server_id` (4), `binlog_filename_len` (4), the file name,
  `binlog_pos` (8); then (the page says: if `BINLOG_THROUGH_GTID`) `data_size` (4) and `data`,
  the encoded GTID set: `n_sids` (8), then per SID its UUID (16), `n_intervals` (8) and the
  intervals, each `start` (8, inclusive) and `end` (8, exclusive) (`Gtid_set::encode`).
  MySQL 8.4 adds a tagged format (`Gtid_format::tagged`): the 8-byte `n_sids` word carries a
  format marker in its top byte (`1`) and the count in bits 8–55, and each SID is followed by its
  tag (a serialization-library varlen length, then the tag bytes; length 0 for no tag). The
  crate's tagged layout is the one in the comments of `n_sids_header`; that the low byte of the
  word is `0` (not `1`) is the crate's choice, see `nSidsHeader`.
* The semi-sync ACK (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_replication_semi_sync.html>,
  MySQL's `ReplSemiSyncSlave`): `0xEF`, the binlog position (8), the binlog file name (the rest).

All integers are little-endian.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- `s` prefixed by its length as one byte (meant for `s.length ≤ 255`). -/
def u8LenStr (s : List U8) : List U8 := byte s.length :: s

/-! ## `COM_REGISTER_SLAVE` -/

/-- A `COM_REGISTER_SLAVE`, as the specs describe it. -/
structure RegSlave where
  serverId : Nat
  hostname : List U8
  user : List U8
  password : List U8
  port : Nat
  rank : Nat
  masterId : Nat
deriving DecidableEq

/-- The `RegSlave` of a `ComRegisterSlave` (all the bytes of the string fields). -/
def RegSlave.of (p : packets.ComRegisterSlave) : RegSlave :=
  ⟨p.server_id.1.val, cowList p.hostname.1, cowList p.user.1, cowList p.password.1,
   p.port.1.val, p.replication_rank.1.val, p.master_id.1.val⟩

/-- The protocol's `COM_REGISTER_SLAVE`. A string field holds at most 255 bytes; longer strings
    are truncated to their first 255 bytes (the crate's documented choice). -/
def regSlaveEnc (r : RegSlave) : List U8 :=
  byte 0x15 :: leBytes 4 r.serverId ++ u8LenStr (r.hostname.take 255) ++ u8LenStr (r.user.take 255)
    ++ u8LenStr (r.password.take 255) ++ leBytes 2 r.port ++ leBytes 4 r.rank ++ leBytes 4 r.masterId

/-- The crate's reader of a `COM_REGISTER_SLAVE` (`ComRegisterSlave::deserialize`): 5 bytes
    (`none`, nothing consumed, if fewer), consumed whatever they hold: `none` if the first is not
    `0x15`, the next four are the server id; the three strings by `checkedLenPrefixed 1`; then 10
    bytes (`none`, nothing more consumed, if fewer). Bytes after them are left unread. -/
def regSlaveRead (bs : List U8) : Option RegSlave × List U8 :=
  if bs.length < 5 then (none, bs)
  else if (bs.getD 0 (byte 0)).val ≠ 0x15 then (none, bs.drop 5)
  else
    let sid := leNat ((bs.drop 1).take 4)
    match checkedLenPrefixed 1 (bs.drop 5) with
    | (none, r) => (none, r)
    | (some h, r) =>
      match checkedLenPrefixed 1 r with
      | (none, r) => (none, r)
      | (some u, r) =>
        match checkedLenPrefixed 1 r with
        | (none, r) => (none, r)
        | (some p, r) =>
          if r.length < 10 then (none, r)
          else (some ⟨sid, h, u, p, leNat (r.take 2), leNat ((r.drop 2).take 4),
            leNat ((r.drop 6).take 4)⟩, r.drop 10)

/-! ## `COM_TABLE_DUMP` -/

/-- The `COM_TABLE_DUMP` of a database and a table name (each truncated to 255 bytes, the crate's
    documented choice). -/
def tableDumpEnc (db tbl : List U8) : List U8 :=
  byte 0x13 :: u8LenStr (db.take 255) ++ u8LenStr (tbl.take 255)

/-- The crate's reader of a `COM_TABLE_DUMP` (`ComTableDump::deserialize`): the header byte
    (`none` on an empty input; `none`, the byte consumed, if not `0x13`), then the two names by
    `checkedLenPrefixed 1`. -/
def tableDumpRead : List U8 → Option (List U8 × List U8) × List U8
  | [] => (none, [])
  | h :: r =>
    if h.val ≠ 0x13 then (none, r)
    else
      match checkedLenPrefixed 1 r with
      | (none, r) => (none, r)
      | (some db, r) =>
        match checkedLenPrefixed 1 r with
        | (none, r) => (none, r)
        | (some tbl, r) => (some (db, tbl), r)

/-! ## `COM_BINLOG_DUMP` -/

/-- The binlog dump flags the crate knows (`BinlogDumpFlags`): `BINLOG_DUMP_NON_BLOCK` (1),
    `BINLOG_THROUGH_POSITION` (2), `BINLOG_THROUGH_GTID` (4). -/
def binlogDumpFlagsAll : Nat := 7

/-- `BINLOG_THROUGH_GTID`. -/
def BINLOG_THROUGH_GTID : Nat := 4

/-- A `COM_BINLOG_DUMP`, as the specs describe it. -/
structure BinlogDump where
  pos : Nat
  flags : Nat
  serverId : Nat
  filename : List U8
deriving DecidableEq

/-- The `BinlogDump` of a `ComBinlogDump`. -/
def BinlogDump.of (p : packets.ComBinlogDump) : BinlogDump :=
  ⟨p.pos.1.val, p.flags.1.val, p.server_id.1.val, cowList p.filename.1⟩

/-- The protocol's `COM_BINLOG_DUMP`. -/
def binlogDumpEnc (d : BinlogDump) : List U8 :=
  byte 0x12 :: leBytes 4 d.pos ++ leBytes 2 d.flags ++ leBytes 4 d.serverId ++ d.filename

/-- The crate's reader of a `COM_BINLOG_DUMP` (`ComBinlogDump::deserialize`): 11 bytes (`none`,
    nothing consumed, if fewer), consumed whatever they hold: `none` if the header is not `0x12`
    or the flags have a bit other than 1, 2, 4; the file name is the rest of the input. **Crate
    behaviour**: flags other than `BINLOG_DUMP_NON_BLOCK` (the only one the command supports)
    are accepted. -/
def binlogDumpRead (bs : List U8) : Option BinlogDump × List U8 :=
  if bs.length < 11 then (none, bs)
  else
    let h := bs.take 11
    let f := leNat ((h.drop 5).take 2)
    if (h.getD 0 (byte 0)).val ≠ 0x12 ∨ f &&& binlogDumpFlagsAll ≠ f then (none, bs.drop 11)
    else (some ⟨leNat ((h.drop 1).take 4), f, leNat ((h.drop 7).take 4), bs.drop 11⟩, [])

/-! ## GTID sets -/

/-- A GNO interval `[start, end)` on the wire. -/
def gnoEnc (g : Nat × Nat) : List U8 := leBytes 8 g.1 ++ leBytes 8 g.2

/-- A SID block entry, as the specs describe it (`Sid`): the UUID, the tag (if any), and the
    intervals as (start, end). -/
structure SidV where
  uuid : List U8
  tag : Option (List U8)
  intervals : List (Nat × Nat)

/-- The `SidV` of a `Sid` (a tag by its bytes). -/
def SidV.of (s : packets.Sid) : SidV :=
  ⟨s.uuid.val, s.tag.map strCowBytes,
   (cowList s.intervals.1).map (fun g => (g.start.1.val, g.«end».1.val))⟩

/-- The intervals on the wire: their number (8 bytes), then each interval. -/
def intervalsEnc (is : List (Nat × Nat)) : List U8 := leBytes 8 is.length ++ is.flatMap gnoEnc

/-- A SID in the untagged format: the UUID, then the intervals (the tag is not sent). -/
def sidEnc (s : SidV) : List U8 := s.uuid ++ intervalsEnc s.intervals

/-- A SID in the tagged format: the UUID, the tag length as a serialization-library varlen
    integer (0 for no tag), the tag bytes, then the intervals. -/
def sidTaggedEnc (s : SidV) : List U8 :=
  s.uuid ++ varlenUint (s.tag.getD []).length ++ s.tag.getD [] ++ intervalsEnc s.intervals

/-- Whether a SID block is sent in the tagged format: some SID has a tag. -/
def gtidTagged (ss : List SidV) : Bool := ss.any (fun s => s.tag.isSome)

/-- The 8-byte `n_sids` word of `n` SIDs: untagged, `n` (bits 0–55, format byte 0); tagged, `n` in
    bits 8–55 and the format byte `1` in bits 56–63. **Crate choice** (unsure against MySQL):
    bits 0–7 of the tagged word are `0` ("reserved" in the crate's comment). -/
def nSidsHeader (tagged : Bool) (n : Nat) : List U8 :=
  if tagged then byte 0 :: leBytes 6 n ++ [byte 1] else leBytes 8 n

/-- The SID block (`data` of `COM_BINLOG_DUMP_GTID`): the `n_sids` word, then the SIDs in the
    format `gtidTagged` chooses. -/
def sidBlock (ss : List SidV) : List U8 :=
  nSidsHeader (gtidTagged ss) ss.length ++ ss.flatMap (if gtidTagged ss then sidTaggedEnc else sidEnc)

/-- A `COM_BINLOG_DUMP_GTID`, as the specs describe it. -/
structure GtidDump where
  flags : Nat
  serverId : Nat
  filename : List U8
  pos : Nat
  sids : List SidV

/-- The `GtidDump` of a `ComBinlogDumpGtid`. -/
def GtidDump.of (g : packets.ComBinlogDumpGtid) : GtidDump :=
  ⟨g.flags.1.val, g.server_id.1.val, cowList g.filename.1, g.pos.1.val,
   (cowList g.sid_block.1).map SidV.of⟩

/-- The `COM_BINLOG_DUMP_GTID` of a request: header, flags, server id, the file name with a
    4-byte length (truncated to `u32::MAX` bytes, the crate's documented choice), position, then
    `data_size` and the SID block. **Crate behaviour**: `data_size` and the SID block are always
    sent, also without `BINLOG_THROUGH_GTID` (the protocol page makes them conditional on that
    flag). -/
def gtidDumpEnc (g : GtidDump) : List U8 :=
  byte 0x1E :: leBytes 2 g.flags ++ leBytes 4 g.serverId
    ++ leBytes 4 (min g.filename.length (2 ^ 32 - 1)) ++ g.filename.take (2 ^ 32 - 1)
    ++ leBytes 8 g.pos ++ leBytes 4 (sidBlock g.sids).length ++ sidBlock g.sids

/-- `n` intervals from the front of `bs` (16 bytes each; meant for `16 * n ≤ bs.length`). -/
def gnoChunks : Nat → List U8 → List (Nat × Nat)
  | 0, _ => []
  | n + 1, bs => (leNat (bs.take 8), leNat ((bs.drop 8).take 8)) :: gnoChunks n (bs.drop 16)

/-- The crate's reader of the intervals of a SID (`Seq<GnoInterval, LeU64>`): the count (8 bytes;
    `none`, nothing consumed, if fewer); **a panic** (unchecked `16 * count` in `usize`) if
    `16 * count` exceeds `usize::MAX`; `none`, the count consumed, if fewer than `16 * count`
    bytes follow; else the intervals. -/
def intervalsRead (bs : List U8) : ReadOut (List (Nat × Nat)) :=
  if bs.length < 8 then .done none bs
  else
    let n := leNat (bs.take 8)
    let r := bs.drop 8
    if Usize.max < 16 * n then .panic .integerOverflow
    else if r.length < 16 * n then .done none r
    else .done (some (gnoChunks n r)) (r.drop (16 * n))

/-- The crate's reader of an untagged SID (`Sid::deserialize`): 16 bytes of UUID (`none`, nothing
    consumed, if fewer), then `intervalsRead`; the tag is `None`. -/
def sidRead (bs : List U8) : ReadOut SidV :=
  if bs.length < 16 then .done none bs
  else
    match intervalsRead (bs.drop 16) with
    | .done (some is) rest => .done (some ⟨bs.take 16, none, is⟩) rest
    | .done none rest => .done none rest
    | .panic e => .panic e
    | .unknown => .unknown

/-- The crate's reader of a tagged SID (`Sid::deserialize_tagged`): 16 bytes of UUID (`none`,
    nothing consumed, if fewer); the tag length (`varlenUintDecode`; `none`, nothing more consumed,
    if malformed); for length 0, no tag; otherwise `none`, nothing more consumed, if fewer bytes
    follow or they are not valid UTF-8, and `none`, the tag consumed, for a tag longer than 32
    bytes (`InvalidTag::TooLong`); then `intervalsRead`. For a valid UTF-8 tag of 1–32 bytes the
    result is `unknown`: `Tag::new` checks its characters through `Chars::next`, an Aeneas-library
    function without a model. -/
def sidTaggedRead (bs : List U8) : ReadOut SidV :=
  if bs.length < 16 then .done none bs
  else
    let uuid := bs.take 16
    let ints (tag : Option (List U8)) (r : List U8) : ReadOut SidV :=
      match intervalsRead r with
      | .done (some is) rest => .done (some ⟨uuid, tag, is⟩) rest
      | .done none rest => .done none rest
      | .panic e => .panic e
      | .unknown => .unknown
    match varlenUintDecode (bs.drop 16) with
    | none => .done none (bs.drop 16)
    | some (tl, r) =>
      if tl = 0 then ints none r
      else if r.length < tl then .done none r
      else if ¬ (Trusted.bytesOf (r.take tl)).IsValidUTF8 then .done none r
      else if 32 < tl then .done none (r.drop tl)
      else .unknown

/-- `n` SIDs read one after the other (tagged or untagged format), stopping at the first failure. -/
def sidsRead (tagged : Bool) : Nat → List U8 → ReadOut (List SidV)
  | 0, bs => .done (some []) bs
  | n + 1, bs =>
    match (if tagged then sidTaggedRead bs else sidRead bs) with
    | .done (some s) rest =>
      match sidsRead tagged n rest with
      | .done (some ss) rest' => .done (some (s :: ss)) rest'
      | .done none rest' => .done none rest'
      | .panic e => .panic e
      | .unknown => .unknown
    | .done none rest => .done none rest
    | .panic e => .panic e
    | .unknown => .unknown

/-- The crate's reader of a `COM_BINLOG_DUMP_GTID` (`ComBinlogDumpGtid::deserialize`):
    * 7 bytes (`none`, nothing consumed, if fewer), consumed whatever they hold: `none` if the
      header is not `0x1E` or the flags have a bit other than 1, 2, 4; then the server id;
    * the file name (`checkedLenPrefixed 4`), the position (8 bytes) and `data_size` (4 bytes)
      (`none`, nothing more consumed, if a field is short);
    * the SID block, `data_size` bytes (`none`, nothing more consumed, if fewer), consumed
      whatever happens inside it: the `n_sids` word (8 bytes, `none` if fewer); its top byte is
      the format: `1` tagged, with the count in bits 8–55; **any other value** untagged, with the
      count in bits 0–55; then that many SIDs (`sidsRead`). Bytes left in the block are ignored.
    **Crate behaviour**: `data_size` and the block are read whatever the flags say. -/
def gtidDumpRead (bs : List U8) : ReadOut GtidDump :=
  if bs.length < 7 then .done none bs
  else
    let h := bs.take 7
    let f := leNat ((h.drop 1).take 2)
    if (h.getD 0 (byte 0)).val ≠ 0x1E ∨ f &&& binlogDumpFlagsAll ≠ f then .done none (bs.drop 7)
    else
      let sid := leNat ((h.drop 3).take 4)
      match checkedLenPrefixed 4 (bs.drop 7) with
      | (none, r) => .done none r
      | (some fname, r) =>
        match readLE 8 r with
        | none => .done none r
        | some (pos, r) =>
          match readLE 4 r with
          | none => .done none r
          | some (len, r) =>
            if r.length < len then .done none r
            else
              let rest := r.drop len
              match readLE 8 (r.take len) with
              | none => .done none rest
              | some (raw, blk) =>
                let tagged := raw / 2 ^ 56 = 1
                let n := if tagged then (raw / 2 ^ 8) % 2 ^ 48 else raw % 2 ^ 56
                match sidsRead tagged n blk with
                | .done (some ss) _ => .done (some ⟨f, sid, fname, pos, ss⟩) rest
                | .done none _ => .done none rest
                | .panic e => .panic e
                | .unknown => .unknown

/-! ## Semi-sync ACK -/

/-- The semi-sync ACK packet. -/
def semiSyncAckEnc (pos : Nat) (filename : List U8) : List U8 :=
  byte 0xEF :: leBytes 8 pos ++ filename

/-- The crate's reader of a semi-sync ACK (`SemiSyncAckPacket::deserialize`): 9 bytes (`none`,
    nothing consumed, if fewer), consumed whatever they hold: `none` if the first is not `0xEF`;
    the next eight are the position; the file name is the rest of the input. -/
def semiSyncAckRead (bs : List U8) : Option (Nat × List U8) × List U8 :=
  if bs.length < 9 then (none, bs)
  else if (bs.getD 0 (byte 0)).val ≠ 0xEF then (none, bs.drop 9)
  else (some (leNat ((bs.drop 1).take 8), bs.drop 9), [])

/-! ## `BinlogRequest` -/

/-- A `BinlogRequest`, as the specs describe it. -/
structure BinlogReq where
  serverId : Nat
  useGtid : Bool
  flags : Nat
  filename : List U8
  pos : Nat
  sids : List SidV

/-- The `BinlogReq` of a `BinlogRequest`. -/
def BinlogReq.of (r : packets.binlog_request.BinlogRequest) : BinlogReq :=
  ⟨r.server_id.val, r.use_gtid, r.flags.val, cowList r.filename, r.pos.val, r.sids.val.map SidV.of⟩

end Defs
