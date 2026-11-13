import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Util.Constants
import Proofs.Misc.Raw.Bytes.U32Bytes
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.VarlenUintSize
import Proofs.Defs.LemmasG
import Proofs.Packets.Sid
import Proofs.Util.Replication

/-! Statements for `struct ComBinlogDumpGtid and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

namespace GtidUtil

@[step] theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  have e : misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d = ok () := by
    simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  rw [e]; exact (WP.spec_ok _).mpr trivial

@[step] theorem rawint_u64_default_spec :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU64.Insts.CoreDefaultDefault
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 core.default.DefaultU64 ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU64.Insts.CoreDefaultDefault
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 core.default.DefaultU64 = ok (0#u64, ()) := by
    simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem const_flags_default_spec :
    misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault = ok (0#u16, ()) := by
    simp [misc.raw._const.Const.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default,
      packets.BinlogDumpFlags.Insts.CoreDefaultDefault.default, packets.BinlogDumpFlags.empty]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

theorem seq_sid_new_vec (v : alloc.vec.Vec packets.Sid) :
    misc.raw.seq.Seq.new misc.raw.int.LeU64 packets.Sid.Insts.CoreCloneClone
      (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
        packets.Sid.Insts.CoreCloneClone)) v = ok (.Owned v, ()) :=
  misc.raw.seq.Seq.new_eq _ _ _ _ _ rfl

@[step] theorem seq_sid_default_spec :
    misc.raw.seq.Seq.Insts.CoreDefaultDefault.default misc.raw.int.LeU64 packets.Sid.Insts.CoreCloneClone
      ⦃ r => cowList r.1 = [] ⦄ := by
  unfold misc.raw.seq.Seq.Insts.CoreDefaultDefault.default
  rw [seq_sid_new_vec]
  exact (WP.spec_ok _).mpr (by simp [cowList, alloc.vec.Vec.new])

@[step] theorem seq_is_empty_spec {T U : Type} (cl : core.clone.Clone T) (s : misc.raw.seq.Seq T U) :
    misc.raw.seq.Seq.is_empty cl s ⦃ b => b = decide (cowList s.1 = []) ⦄ := by
  unfold misc.raw.seq.Seq.is_empty
  obtain ⟨c, u⟩ := s
  step with cow_deref_spec as ⟨sl, hsl⟩
  simp [core.slice.Slice.is_empty, hsl]

@[step] theorem flags_remove_spec (f g : packets.BinlogDumpFlags) :
    packets.BinlogDumpFlags.remove f g ⦃ r => r.val = andNot 16 f.val g.val ⦄ := by
  simp [packets.BinlogDumpFlags.remove, packets.BinlogDumpFlags.difference, lift, andNot,
    ConstUtil.u16_val_not]

@[step] theorem flags_insert_spec (f g : packets.BinlogDumpFlags) :
    packets.BinlogDumpFlags.insert f g ⦃ r => r.val = f.val ||| g.val ⦄ := by
  simp [packets.BinlogDumpFlags.insert, packets.BinlogDumpFlags.union, lift]

theorem through_gtid_val : (packets.BinlogDumpFlags.BINLOG_THROUGH_GTID : U16).val = BINLOG_THROUGH_GTID := by
  simp [packets.BinlogDumpFlags.BINLOG_THROUGH_GTID, BINLOG_THROUGH_GTID]

theorem u32bytes_as_bytes_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U32Bytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = (cowList rb.1).take (2 ^ 32 - 1) ⦄ := by
  have ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm rb)
  intro s hs; rw [hs, hmv]

theorem u32bytes_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U32Bytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid ((cowList rb.1).take (2 ^ 32 - 1)) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with u32bytes_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

end GtidUtil

open GtidUtil

/-- `ComBinlogDumpGtid::new(server_id)`: no flags, the server id, an empty file name, position
    0, no SIDs. -/
theorem packets.ComBinlogDumpGtid.new_spec (server_id : U32) :
    packets.ComBinlogDumpGtid.new server_id ⦃ g =>
      GtidDump.of g = ⟨0, server_id.val, [], 0, []⟩ ⦄ := by
  unfold packets.ComBinlogDumpGtid.new
  step*
  simp_all [GtidDump.of]

/-- `server_id`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.server_id_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.server_id self = ok self.server_id.1 := by
  rfl

/-- `flags`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.flags_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.flags self = ok self.flags.1 := by
  rfl

/-- `filename_raw`: the file name's effective bytes (at most the first `u32::MAX`). -/
theorem packets.ComBinlogDumpGtid.filename_raw_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.filename_raw self ⦃ s =>
      s.val = (cowList self.filename.1).take (2 ^ 32 - 1) ⦄ := by
  exact u32bytes_as_bytes_spec _

/-- `filename`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComBinlogDumpGtid.impl.filename_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.filename self ⦃ c =>
      LossyUtf8Valid ((cowList self.filename.1).take (2 ^ 32 - 1)) c ⦄ := by
  exact u32bytes_as_str_spec _

/-- `pos`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.pos_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.pos self = ok self.pos.1 := by
  rfl

/-- `sids`: the SIDs. -/
theorem packets.ComBinlogDumpGtid.sids_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.sids self ⦃ s => s.val = cowList self.sid_block.1 ⦄ := by
  unfold packets.ComBinlogDumpGtid.sids
  exact misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec _ _

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
theorem packets.ComBinlogDumpGtid.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDumpGtid) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_filename into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with filename := cowList c } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_filename
  step*
  simp_all [GtidDump.of]

/-- `with_server_id`: sets the server id; nothing else changes. -/
theorem packets.ComBinlogDumpGtid.with_server_id_spec (self : packets.ComBinlogDumpGtid) (server_id : U32) :
    packets.ComBinlogDumpGtid.with_server_id self server_id ⦃ g =>
      GtidDump.of g = { GtidDump.of self with serverId := server_id.val } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_server_id
  simp [GtidDump.of]

/-- `with_flags(flags)`: sets the flags, with `BINLOG_THROUGH_GTID` set exactly when there are
    SIDs; nothing else changes. -/
theorem packets.ComBinlogDumpGtid.with_flags_spec (self : packets.ComBinlogDumpGtid)
    (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDumpGtid.with_flags self flags ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList self.sid_block.1 = [] then andNot 16 flags.val BINLOG_THROUGH_GTID
                 else flags.val ||| BINLOG_THROUGH_GTID } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_flags
  step*
  · simp_all [GtidDump.of, through_gtid_val]
  · simp_all [GtidDump.of, through_gtid_val]

/-- `with_pos`: sets the position; nothing else changes. -/
theorem packets.ComBinlogDumpGtid.with_pos_spec (self : packets.ComBinlogDumpGtid) (pos : U64) :
    packets.ComBinlogDumpGtid.with_pos self pos ⦃ g =>
      GtidDump.of g = { GtidDump.of self with pos := pos.val } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_pos
  simp [GtidDump.of]

/-- `with_sid(sid)`: appends the SID and sets `BINLOG_THROUGH_GTID`; nothing else changes.
    (Preconditions: room for one more SID, and tags that fit in a `usize`, as every real
    string does: a borrowed block is cloned first.) -/
theorem packets.ComBinlogDumpGtid.with_sid_spec (self : packets.ComBinlogDumpGtid) (sid : packets.Sid)
    (h : (cowList self.sid_block.1).length < Usize.max)
    (htags : ∀ s ∈ (GtidDump.of self).sids, ∀ t, s.tag = some t → t.length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.with_sid self sid ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (GtidDump.of self).sids ++ [SidV.of sid] } ⦄ := by
  sorry

/-- `with_sids(sids)`: replaces the SIDs (`sids.into()`), with `BINLOG_THROUGH_GTID` set exactly
    when there are SIDs; nothing else changes. -/
theorem packets.ComBinlogDumpGtid.with_sids_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)))
    (self : packets.ComBinlogDumpGtid) (x : T)
    (c : alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)) (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_sids into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList c = [] then andNot 16 (GtidDump.of self).flags BINLOG_THROUGH_GTID
                 else (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (cowList c).map SidV.of } ⦄ := by
  sorry

/-- `MySerialize for ComBinlogDumpGtid`: appends `gtidDumpEnc`: the file name with a 4-byte
    length, the position, `data_size` and the SID block (tagged format iff some SID has a tag;
    `data_size` and the block are sent even without `BINLOG_THROUGH_GTID`). Precondition: the
    SID block is shorter than `2^32` bytes; otherwise **crate behaviour**: `data_size` is
    computed with saturating (and truncating `as u32`) arithmetic and no longer matches the
    block. -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDumpGtid) (buf : alloc.vec.Vec U8)
    (hblk : (sidBlock (GtidDump.of self).sids).length < 2 ^ 32)
    (h : buf.length + (gtidDumpEnc (GtidDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gtidDumpEnc (GtidDump.of self) ⦄ := by
  sorry

/-- `MyDeserialize for ComBinlogDumpGtid`: `SIZE` is `None`. -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ComBinlogDumpGtid`: exactly `gtidDumpRead` whenever that reader returns.
    It does in the untagged format, and in the tagged format until it meets a non-empty tag
    (`unknown`: the tag's character check is not modelled, see `sidTaggedRead`).
    It is never `unknown` in the untagged format (`Defs.sidsRead_untagged_ne_unknown`), and in
    the tagged format only through a tag of 1–32 valid UTF-8 bytes
    (`Defs.gtidDumpRead_unknown`, `Defs.sidTaggedRead_unknown_iff`).
    **Allocation caveat (GTID).** The SID count comes from the input (up to `2^56`) and is passed
    to `Vec::with_capacity` before any SID is read, which the model treats as free: in real Rust
    a 31-byte packet announcing `2^56` SIDs makes the reader try to allocate `2^56` SIDs and
    abort the process (out of memory, observed), where the model returns an error. The same
    holds for each SID's interval count (`Sid::deserialize_overflow`). -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) (r0 : Option GtidDump) (rest0 : List U8)
    (h : gtidDumpRead buf.val = .done r0 rest0) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = r0 ∧ rest.val = rest0 ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for ComBinlogDumpGtid` panics where `gtidDumpRead` does: a SID
    whose interval count `n` has `16 * n` above `usize::MAX` (see `Sid::deserialize_overflow`:
    real Rust crashes earlier, in `Vec::with_capacity`). -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (h64 : Target64) (buf : io.ParseBuf) (e : Error) (h : gtidDumpRead buf.val = .panic e) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e := by
  sorry

/-- Round trip (untagged format): a request without tags, with known flags, a file name shorter
    than `2^32` bytes and a SID block shorter than `2^32` bytes, is read back from
    `gtidDumpEnc`. (With a tag, see `deserialize_spec`.) -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (g : packets.ComBinlogDumpGtid)
    (hnotag : gtidTagged (GtidDump.of g).sids = false)
    (hf : (GtidDump.of g).flags &&& binlogDumpFlagsAll = (GtidDump.of g).flags)
    (hfn : (GtidDump.of g).filename.length < 2 ^ 32)
    (hblk : (sidBlock (GtidDump.of g).sids).length < 2 ^ 32)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidDumpEnc (GtidDump.of g) ++ tail) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = some (GtidDump.of g) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
