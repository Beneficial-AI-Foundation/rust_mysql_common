import Defs

/-! Statements for `struct BinlogRequest and its impls` (spec file:
`Specs/Packets/BinlogRequest.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `BinlogRequest::new(server_id)`: the server id, `COM_BINLOG_DUMP` (no GTID), no flags, an
    empty file name, position 4 (documented default), no SIDs. -/
theorem packets.binlog_request.BinlogRequest.new_spec (server_id : U32) :
    packets.binlog_request.BinlogRequest.new server_id ⦃ r =>
      BinlogReq.of r = ⟨server_id.val, false, 0, [], 4, []⟩ ⦄ := by
  sorry

/-- `server_id`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.server_id_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.server_id self = ok self.server_id := by
  sorry

/-- `use_gtid`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.use_gtid_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.use_gtid self = ok self.use_gtid := by
  sorry

/-- `flags`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.flags_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.flags self = ok self.flags := by
  sorry

/-- `filename_raw`: the file name. -/
theorem packets.binlog_request.BinlogRequest.filename_raw_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.filename_raw self ⦃ s => s.val = cowList self.filename ⦄ := by
  sorry

/-- `filename`: the file name's raw bytes. **Quirk**: documented as "a UTF-8 string (lossy
    converted)", it returns the same bytes as `filename_raw`. -/
theorem packets.binlog_request.BinlogRequest.impl.filename_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.filename self ⦃ s => s.val = cowList self.filename ⦄ := by
  sorry

/-- `pos`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.pos_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.pos self = ok self.pos := by
  sorry

/-- `sids`: the SIDs. -/
theorem packets.binlog_request.BinlogRequest.impl.sids_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.sids self ⦃ s => s.val = self.sids.val ⦄ := by
  sorry

/-- `with_server_id`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_server_id_eq (self : packets.binlog_request.BinlogRequest)
    (server_id : U32) :
    packets.binlog_request.BinlogRequest.with_server_id self server_id = ok { self with server_id } := by
  sorry

/-- `with_use_gtid`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_use_gtid_eq (self : packets.binlog_request.BinlogRequest)
    (use_gtid : Bool) :
    packets.binlog_request.BinlogRequest.with_use_gtid self use_gtid = ok { self with use_gtid } := by
  sorry

/-- `with_flags`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_flags_eq (self : packets.binlog_request.BinlogRequest)
    (flags : packets.BinlogDumpFlags) :
    packets.binlog_request.BinlogRequest.with_flags self flags = ok { self with flags } := by
  sorry

/-- `with_filename`: sets the field to `filename.into()`. -/
theorem packets.binlog_request.BinlogRequest.with_filename_eq {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.binlog_request.BinlogRequest) (x : T)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into x = ok c) :
    packets.binlog_request.BinlogRequest.with_filename into self x = ok { self with filename := c } := by
  sorry

/-- `with_pos`: sets the field to `pos.into()`. -/
theorem packets.binlog_request.BinlogRequest.with_pos_eq {T : Type} (into : core.convert.Into T U64)
    (self : packets.binlog_request.BinlogRequest) (x : T) (p : U64) (h : into.into x = ok p) :
    packets.binlog_request.BinlogRequest.with_pos into self x = ok { self with pos := p } := by
  sorry

/-- `as_cmd`: without GTID, a `COM_BINLOG_DUMP` with the position **truncated to 32 bits**
    (`pos as u32`, documented), only the `BINLOG_DUMP_NON_BLOCK` flag kept (documented), the
    server id and the file name (the SIDs are ignored); with GTID, a `COM_BINLOG_DUMP_GTID` with
    the flags, `BINLOG_THROUGH_GTID` set exactly when there are SIDs, the server id, the file
    name, the position and the SIDs. -/
theorem packets.binlog_request.BinlogRequest.as_cmd_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.as_cmd self ⦃ e =>
      match e with
      | .Left d => self.use_gtid = false ∧
          BinlogDump.of d = ⟨self.pos.val % 2 ^ 32, self.flags.val &&& 1, self.server_id.val,
            cowList self.filename⟩
      | .Right g => self.use_gtid = true ∧
          GtidDump.of g = ⟨if self.sids.val = [] then andNot 16 self.flags.val BINLOG_THROUGH_GTID
              else self.flags.val ||| BINLOG_THROUGH_GTID,
            self.server_id.val, cowList self.filename, self.pos.val, self.sids.val.map SidV.of⟩ ⦄ := by
  sorry

end mysql_common
