import Defs

/-! Statements for `struct ProgressReport and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given fields (the stage info converted with `into`). -/
theorem packets.ProgressReport.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (stage max_stage : U8) (progress : U32) (stage_info : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into stage_info = ok c) :
    packets.ProgressReport.new into stage max_stage progress stage_info ⦃ p =>
      p.stage.1 = stage ∧ p.max_stage.1 = max_stage ∧ p.progress.1 = progress ∧ p.stage_info.1 = c ⦄ := by
  sorry

/-- `stage`: the field. -/
theorem packets.ProgressReport.impl.stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.stage self = ok self.stage.1 := by
  sorry

/-- `max_stage`: the field. -/
theorem packets.ProgressReport.impl.max_stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.max_stage self = ok self.max_stage.1 := by
  sorry

/-- `progress`: the field. -/
theorem packets.ProgressReport.impl.progress_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.progress self = ok self.progress.1 := by
  sorry

/-- `stage_info_ref`: the stage info bytes. -/
theorem packets.ProgressReport.stage_info_ref_spec (self : packets.ProgressReport) :
    packets.ProgressReport.stage_info_ref self ⦃ s => s.val = cowList self.stage_info.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields. -/
theorem packets.ProgressReport.into_owned_spec (self : packets.ProgressReport) :
    packets.ProgressReport.into_owned self ⦃ p => Progress.of p = Progress.of self ⦄ := by
  sorry

/-- `MyDeserialize for ProgressReport`: `SIZE` is `None`. -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ProgressReport`: total; `progressRead`. -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Progress.of, rest.val) = progressRead buf.val ⦄ := by
  sorry

/-- `MySerialize for ProgressReport`: appends `progressEnc` (the progress truncated to 3 bytes). -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ProgressReport) (buf : alloc.vec.Vec U8)
    (h : buf.length + (progressEnc (Progress.of self)).length ≤ Usize.max) :
    packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ progressEnc (Progress.of self) ⦄ := by
  sorry

/-- Round trip: `deserialize` reads back what `serialize` writes, when the progress fits in 3 bytes. -/
theorem packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (p : packets.ProgressReport) (hp : p.progress.1.val < 2 ^ 24) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = progressEnc (Progress.of p) ++ tail) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Progress.of = some (Progress.of p) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
