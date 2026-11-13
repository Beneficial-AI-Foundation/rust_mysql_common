import Defs

/-! Statements for `struct GnoInterval and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `GnoInterval::new(start, end)`: the two bounds, unchecked. -/
theorem packets.GnoInterval.new_spec (start «end» : U64) :
    packets.GnoInterval.new start «end» ⦃ g => g.start.1 = start ∧ g.«end».1 = «end» ⦄ := by
  sorry

/-- `start`: the start (inclusive). -/
theorem packets.GnoInterval.impl.start_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.start self = ok self.start.1 := by
  sorry

/-- `end`: the end (exclusive). -/
theorem packets.GnoInterval.impl.end_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.end self = ok self.«end».1 := by
  sorry

/-- `check_and_new(start, end)`: total; an error iff the interval `[start, end)` is empty or
    contains 0 (`start ≥ end` or `start = 0`; GNOs start at 1), else the interval. -/
theorem packets.GnoInterval.check_and_new_spec (start «end» : U64) :
    packets.GnoInterval.check_and_new start «end» ⦃ r =>
      if «end».val ≤ start.val ∨ start.val = 0 then okPart r = none
      else ∃ g, r = .Ok g ∧ g.start.1 = start ∧ g.«end».1 = «end» ⦄ := by
  sorry

/-- `MySerialize for GnoInterval`: appends `gnoEnc` (start, end, 8 bytes each). -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.GnoInterval) (buf : alloc.vec.Vec U8) (h : buf.length + 16 ≤ Usize.max) :
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gnoEnc (self.start.1.val, self.«end».1.val) ⦄ := by
  sorry

/-- `MyDeserialize for GnoInterval`: `SIZE` is `Some(16)`. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 16#usize := by
  sorry

/-- `MyDeserialize for GnoInterval`: reads 16 bytes (start, end). Unchecked: it panics on a
    shorter buffer (`deserialize_panics`); `parse` checks through `SIZE`. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun g => (g.start.1.val, g.«end».1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧
      rest.val = buf.val.drop 16 ⦄ := by
  sorry

/-- `MyDeserialize for GnoInterval` panics on fewer than 16 bytes. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (buf : io.ParseBuf) (h : buf.length < 16) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .panic := by
  sorry

end mysql_common
