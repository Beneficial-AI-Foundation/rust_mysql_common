import Proofs.Packets.BinlogRequest.BinlogRequest

/-!
# `src/packets/binlog_request.rs`
    `BinlogRequest`, the builder of `COM_BINLOG_DUMP` / `COM_BINLOG_DUMP_GTID` requests: its
    defaults, accessors, `with_*` setters and `as_cmd`.

    **Patches.** 61 (`BinlogDumpFlags` as plain bitflags). The statements are about the patched
    code.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/BinlogCmd.lean` (`BinlogReq`, `BinlogDump`, `GtidDump`, `SidV`,
    `BINLOG_THROUGH_GTID`), `Defs/Flags.lean` (`andNot`), `Defs/Bytes.lean`.

    **Trusted axioms.** None beyond the standard ones.

    **Not covered.** `with_sids` (generic over `IntoIterator`; not translated); derived traits.

    **Behaviour to note.**
    * `as_cmd` without GTID truncates the position to 32 bits and keeps only
      `BINLOG_DUMP_NON_BLOCK` (both documented); with GTID it sets `BINLOG_THROUGH_GTID`
      exactly when there are SIDs, whatever the flags say.
    * `filename` is documented as a lossily converted string but returns the raw bytes, like
      `filename_raw`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct BinlogRequest and its impls` -/

/-- `BinlogRequest::new(server_id)`: the server id, `COM_BINLOG_DUMP` (no GTID), no flags, an
    empty file name, position 4 (documented default), no SIDs. -/
recall packets.binlog_request.BinlogRequest.new_spec (server_id : U32) :
    packets.binlog_request.BinlogRequest.new server_id ⦃ r =>
      BinlogReq.of r = ⟨server_id.val, false, 0, [], 4, []⟩ ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.new_spec
/-- `server_id`: the field. -/
recall packets.binlog_request.BinlogRequest.impl.server_id_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.server_id self = ok self.server_id

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.server_id_eq
/-- `use_gtid`: the field. -/
recall packets.binlog_request.BinlogRequest.impl.use_gtid_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.use_gtid self = ok self.use_gtid

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.use_gtid_eq
/-- `flags`: the field. -/
recall packets.binlog_request.BinlogRequest.impl.flags_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.flags self = ok self.flags

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.flags_eq
/-- `filename_raw`: the file name. -/
recall packets.binlog_request.BinlogRequest.filename_raw_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.filename_raw self ⦃ s => s.val = cowList self.filename ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.filename_raw_spec
/-- `filename`: the file name's raw bytes. **Quirk**: documented as "a UTF-8 string (lossy
    converted)", it returns the same bytes as `filename_raw`. -/
recall packets.binlog_request.BinlogRequest.impl.filename_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.filename self ⦃ s => s.val = cowList self.filename ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.filename_spec
/-- `pos`: the field. -/
recall packets.binlog_request.BinlogRequest.impl.pos_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.pos self = ok self.pos

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.pos_eq
/-- `sids`: the SIDs. -/
recall packets.binlog_request.BinlogRequest.impl.sids_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.sids self ⦃ s => s.val = self.sids.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.impl.sids_spec
/-- `with_server_id`: sets the field. -/
recall packets.binlog_request.BinlogRequest.with_server_id_eq (self : packets.binlog_request.BinlogRequest)
    (server_id : U32) :
    packets.binlog_request.BinlogRequest.with_server_id self server_id = ok { self with server_id }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.with_server_id_eq
/-- `with_use_gtid`: sets the field. -/
recall packets.binlog_request.BinlogRequest.with_use_gtid_eq (self : packets.binlog_request.BinlogRequest)
    (use_gtid : Bool) :
    packets.binlog_request.BinlogRequest.with_use_gtid self use_gtid = ok { self with use_gtid }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.with_use_gtid_eq
/-- `with_flags`: sets the field. -/
recall packets.binlog_request.BinlogRequest.with_flags_eq (self : packets.binlog_request.BinlogRequest)
    (flags : packets.BinlogDumpFlags) :
    packets.binlog_request.BinlogRequest.with_flags self flags = ok { self with flags }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.with_flags_eq
/-- `with_filename`: sets the field to `filename.into()`. -/
recall packets.binlog_request.BinlogRequest.with_filename_eq {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.binlog_request.BinlogRequest) (x : T)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into x = ok c) :
    packets.binlog_request.BinlogRequest.with_filename into self x = ok { self with filename := c }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.with_filename_eq
/-- `with_pos`: sets the field to `pos.into()`. -/
recall packets.binlog_request.BinlogRequest.with_pos_eq {T : Type} (into : core.convert.Into T U64)
    (self : packets.binlog_request.BinlogRequest) (x : T) (p : U64) (h : into.into x = ok p) :
    packets.binlog_request.BinlogRequest.with_pos into self x = ok { self with pos := p }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.with_pos_eq
/-- `as_cmd`: without GTID, a `COM_BINLOG_DUMP` with the position **truncated to 32 bits**
    (`pos as u32`, documented), only the `BINLOG_DUMP_NON_BLOCK` flag kept (documented), the
    server id and the file name (the SIDs are ignored); with GTID, a `COM_BINLOG_DUMP_GTID` with
    the flags, `BINLOG_THROUGH_GTID` set exactly when there are SIDs, the server id, the file
    name, the position and the SIDs. -/
recall packets.binlog_request.BinlogRequest.as_cmd_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.as_cmd self ⦃ e =>
      match e with
      | .Left d => self.use_gtid = false ∧
          BinlogDump.of d = ⟨self.pos.val % 2 ^ 32, self.flags.val &&& 1, self.server_id.val,
            cowList self.filename⟩
      | .Right g => self.use_gtid = true ∧
          GtidDump.of g = ⟨if self.sids.val = [] then andNot 16 self.flags.val BINLOG_THROUGH_GTID
              else self.flags.val ||| BINLOG_THROUGH_GTID,
            self.server_id.val, cowList self.filename, self.pos.val, self.sids.val.map SidV.of⟩ ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.binlog_request.BinlogRequest.as_cmd_spec
end mysql_common
