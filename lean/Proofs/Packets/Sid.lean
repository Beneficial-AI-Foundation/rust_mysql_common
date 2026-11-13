import Defs

/-! Statements for `struct Sid and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Sid::new(uuid)`: the UUID, no tag, no intervals. -/
theorem packets.Sid.new_spec (uuid : Array U8 16#usize) :
    packets.Sid.new uuid ⦃ s => SidV.of s = ⟨uuid.val, none, []⟩ ⦄ := by
  sorry

/-- `uuid`: the field. -/
theorem packets.Sid.impl.uuid_eq (self : packets.Sid) :
    packets.Sid.impl.uuid self = ok self.uuid := by
  sorry

/-- `tag`: the field. -/
theorem packets.Sid.impl.tag_eq (self : packets.Sid) :
    packets.Sid.impl.tag self = ok self.tag := by
  sorry

/-- `intervals`: the intervals. -/
theorem packets.Sid.impl.intervals_spec (self : packets.Sid) :
    packets.Sid.impl.intervals self ⦃ s => s.val = cowList self.intervals.1 ⦄ := by
  sorry

/-- `with_interval(g)`: appends the interval (unchecked); nothing else changes. (Precondition:
    room for one more interval.) -/
theorem packets.Sid.with_interval_spec (self : packets.Sid) (g : packets.GnoInterval)
    (h : (cowList self.intervals.1).length < Usize.max) :
    packets.Sid.with_interval self g ⦃ s =>
      SidV.of s = { SidV.of self with
        intervals := (SidV.of self).intervals ++ [(g.start.1.val, g.«end».1.val)] } ⦄ := by
  sorry

/-- `with_intervals(v)`: replaces the intervals (unchecked); nothing else changes. -/
theorem packets.Sid.with_intervals_spec (self : packets.Sid) (v : alloc.vec.Vec packets.GnoInterval) :
    packets.Sid.with_intervals self v ⦃ s =>
      SidV.of s = { SidV.of self with intervals := v.val.map (fun g => (g.start.1.val, g.«end».1.val)) } ⦄ := by
  sorry

/-- `with_tag(t)`: sets the tag. -/
theorem packets.Sid.with_tag_eq (self : packets.Sid) (t : packets.Tag) :
    packets.Sid.with_tag self t = ok { self with tag := some t } := by
  sorry

/-- `MySerialize for Sid`: appends the untagged format `sidEnc` (UUID, interval count,
    intervals). **The tag is not written** (the tagged format is written only by
    `ComBinlogDumpGtid`). -/
theorem packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Sid)
    (buf : alloc.vec.Vec U8) (h : buf.length + (sidEnc (SidV.of self)).length ≤ Usize.max) :
    packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ sidEnc (SidV.of self) ⦄ := by
  sorry

/-- `MyDeserialize for Sid`: `SIZE` is `None`. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for Sid`: the untagged format (`sidRead`; the tag is `None`), exactly,
    whenever that reader returns. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) (r0 : Option SidV) (rest0 : List U8) (h : sidRead buf.val = .done r0 rest0) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = r0 ∧ rest.val = rest0 ⦄ := by
  sorry

/-- **Crash path.** In the model, `MyDeserialize for Sid` panics where `sidRead` does: an
    interval count `n` from the input with `16 * n` above `usize::MAX` (`n ≥ 2^60`, unchecked
    multiplication). **Real Rust crashes earlier and more often**: `Vec::with_capacity(n)` runs
    first, before the count is checked against the input, so a large count aborts the process
    (out of memory), and `n ≥ 2^59` panics (capacity overflow), on a ~24-byte input; the model
    treats the allocation as free (allocation caveat) and returns an error for `n < 2^60`. The
    model's `16 * n` overflow is never reached in real Rust. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_overflow (h64 : Target64)
    (buf : io.ParseBuf) (e : Error) (h : sidRead buf.val = .panic e) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e := by
  sorry

/-- Round trip: the untagged format is read back, without the tag. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64)
    (s : packets.Sid) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sidEnc (SidV.of s) ++ tail) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = some { SidV.of s with tag := none } ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
