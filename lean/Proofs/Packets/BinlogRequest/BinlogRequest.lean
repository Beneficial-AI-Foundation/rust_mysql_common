import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Packets.ComBinlogDump
import Proofs.Packets.ComBinlogDumpGtid
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Util.Constants
import Proofs.Misc.Raw.Seq.Seq

/-! Statements for `struct BinlogRequest and its impls` (spec file:
`Specs/Packets/BinlogRequest.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

/-- `BinlogRequest::new(server_id)`: the server id, `COM_BINLOG_DUMP` (no GTID), no flags, an
    empty file name, position 4 (documented default), no SIDs. -/
theorem packets.binlog_request.BinlogRequest.new_spec (server_id : U32) :
    packets.binlog_request.BinlogRequest.new server_id ⦃ r =>
      BinlogReq.of r = ⟨server_id.val, false, 0, [], 4, []⟩ ⦄ := by
  simp [packets.binlog_request.BinlogRequest.new, packets.BinlogDumpFlags.empty,
    alloc.borrow.Cow.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default, BinlogReq.of, cowList, alloc.vec.Vec.new]

/-- `server_id`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.server_id_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.server_id self = ok self.server_id := by
  rfl

/-- `use_gtid`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.use_gtid_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.use_gtid self = ok self.use_gtid := by
  rfl

/-- `flags`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.flags_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.flags self = ok self.flags := by
  rfl

/-- `filename_raw`: the file name. -/
theorem packets.binlog_request.BinlogRequest.filename_raw_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.filename_raw self ⦃ s => s.val = cowList self.filename ⦄ := by
  unfold packets.binlog_request.BinlogRequest.filename_raw
  exact cow_as_ref_spec _ _

/-- `filename`: the file name's raw bytes. **Quirk**: documented as "a UTF-8 string (lossy
    converted)", it returns the same bytes as `filename_raw`. -/
theorem packets.binlog_request.BinlogRequest.impl.filename_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.filename self ⦃ s => s.val = cowList self.filename ⦄ := by
  unfold packets.binlog_request.BinlogRequest.impl.filename
  exact cow_as_ref_spec _ _

/-- `pos`: the field. -/
theorem packets.binlog_request.BinlogRequest.impl.pos_eq (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.pos self = ok self.pos := by
  rfl

/-- `sids`: the SIDs. -/
theorem packets.binlog_request.BinlogRequest.impl.sids_spec (self : packets.binlog_request.BinlogRequest) :
    packets.binlog_request.BinlogRequest.impl.sids self ⦃ s => s.val = self.sids.val ⦄ := by
  simp [packets.binlog_request.BinlogRequest.impl.sids, alloc.vec.Vec.deref]

/-- `with_server_id`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_server_id_eq (self : packets.binlog_request.BinlogRequest)
    (server_id : U32) :
    packets.binlog_request.BinlogRequest.with_server_id self server_id = ok { self with server_id } := by
  rfl

/-- `with_use_gtid`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_use_gtid_eq (self : packets.binlog_request.BinlogRequest)
    (use_gtid : Bool) :
    packets.binlog_request.BinlogRequest.with_use_gtid self use_gtid = ok { self with use_gtid } := by
  rfl

/-- `with_flags`: sets the field. -/
theorem packets.binlog_request.BinlogRequest.with_flags_eq (self : packets.binlog_request.BinlogRequest)
    (flags : packets.BinlogDumpFlags) :
    packets.binlog_request.BinlogRequest.with_flags self flags = ok { self with flags } := by
  rfl

/-- `with_filename`: sets the field to `filename.into()`. -/
theorem packets.binlog_request.BinlogRequest.with_filename_eq {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.binlog_request.BinlogRequest) (x : T)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into x = ok c) :
    packets.binlog_request.BinlogRequest.with_filename into self x = ok { self with filename := c } := by
  simp [packets.binlog_request.BinlogRequest.with_filename, h]

/-- `with_pos`: sets the field to `pos.into()`. -/
theorem packets.binlog_request.BinlogRequest.with_pos_eq {T : Type} (into : core.convert.Into T U64)
    (self : packets.binlog_request.BinlogRequest) (x : T) (p : U64) (h : into.into x = ok p) :
    packets.binlog_request.BinlogRequest.with_pos into self x = ok { self with pos := p } := by
  simp [packets.binlog_request.BinlogRequest.with_pos, h]



private theorem andNot4_idem (x : Nat) : andNot 16 (andNot 16 x 4) 4 = andNot 16 x 4 := by
  simp [andNot]

private theorem andNot4_or (f : U16) : andNot 16 f.val 4 ||| 4 = f.val ||| 4 := by
  have hf : f.val < 2 ^ 16 := by scalar_tac
  simp only [andNot]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and]
  by_cases hi : i < 16
  · have h4 : ∀ j < 16, (2 ^ 16 - 1 - 4 % 2 ^ 16).testBit j = !decide (j = 2) := by decide
    have h4' : ∀ j < 16, (4 : Nat).testBit j = decide (j = 2) := by decide
    rw [h4 i hi, h4' i hi]
    by_cases h2 : i = 2 <;> simp [h2]
  · have : f.val.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hf (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

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
  unfold packets.binlog_request.BinlogRequest.as_cmd packets.binlog_request.BinlogRequest.impl.use_gtid
  cases hg : self.use_gtid
  · simp only [bind_ok, Bool.false_eq_true, ite_false]
    apply WP.spec_bind (packets.ComBinlogDump.new_spec self.server_id)
    intro d0 h0
    simp only [lift, bind_ok]
    apply WP.spec_bind (packets.ComBinlogDump.with_pos_spec d0 (UScalar.cast .U32 self.pos))
    intro d1 h1
    apply WP.spec_bind (cow_deref_spec _ self.filename)
    intro s hs
    apply WP.spec_bind (packets.ComBinlogDump.with_filename_spec _ d1 s (.Borrowed s) rfl)
    intro d2 h2
    have hb : packets.BinlogDumpFlags.Insts.CoreOpsBitBitAndBinlogDumpFlagsBinlogDumpFlags.bitand self.flags
        packets.BinlogDumpFlags.BINLOG_DUMP_NON_BLOCK = ok (self.flags &&& 1#u16) := by
      simp [packets.BinlogDumpFlags.Insts.CoreOpsBitBitAndBinlogDumpFlagsBinlogDumpFlags.bitand,
        packets.BinlogDumpFlags.intersection, packets.BinlogDumpFlags.BINLOG_DUMP_NON_BLOCK, lift]
    rw [hb, bind_ok]
    apply WP.spec_bind (packets.ComBinlogDump.with_flags_spec d2 _)
    intro d3 h3
    simp only [WP.spec_ok]
    refine ⟨trivial, ?_⟩
    rw [h3, h2, h1, h0]
    simp [UScalar.cast_val_eq, UScalar.val_and, cowList, hs]
  · simp only [bind_ok, ite_true]
    apply WP.spec_bind (packets.ComBinlogDumpGtid.new_spec self.server_id)
    intro g0 h0
    apply WP.spec_bind (packets.ComBinlogDumpGtid.with_pos_spec g0 self.pos)
    intro g1 h1
    apply WP.spec_bind (packets.ComBinlogDumpGtid.with_flags_spec g1 self.flags)
    intro g2 h2
    apply WP.spec_bind (cow_deref_spec _ self.filename)
    intro s hs
    apply WP.spec_bind (packets.ComBinlogDumpGtid.with_filename_spec _ g2 s (.Borrowed s) rfl)
    intro g3 h3
    apply WP.spec_bind (packets.ComBinlogDumpGtid.with_sids_spec _ g3 _
      (.Borrowed (alloc.vec.Vec.deref self.sids)) rfl)
    intro g4 h4
    simp only [WP.spec_ok]
    refine ⟨trivial, ?_⟩
    have he : cowList g1.sid_block.1 = [] := by
      have := congrArg GtidDump.sids (h1.trans (congrArg (fun x => { x with pos := self.pos.val }) h0))
      simpa [GtidDump.of] using this
    rw [h4, h3, h2, he]
    have h1' := congrArg GtidDump.serverId h1
    have h1p := congrArg GtidDump.pos h1
    simp only [h0] at h1'
    simp only [GtidDump.mk.injEq]
    by_cases hsd : self.sids.val = []
    · simp [hsd, cowList, alloc.vec.Vec.deref, andNot4_idem, hs, h1', h1p, BINLOG_THROUGH_GTID]
    · simp [hsd, cowList, alloc.vec.Vec.deref, andNot4_or, hs, h1', h1p, BINLOG_THROUGH_GTID]

end mysql_common
