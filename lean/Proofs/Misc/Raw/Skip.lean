import Proofs.Util.IntAndMisc

/-! Statements for `struct Skip<LEN> and its impls` (spec file: `Specs/Misc/Raw.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `MyDeserialize for Skip<LEN>`: `SIZE` is `Some(LEN)`. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN := by
  unfold misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for Skip<LEN>`: skips `LEN` bytes. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).isSome ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  unfold misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.skip_spec as ⟨ rest, hr ⟩
  simp [okPart, hr]

/-- `MyDeserialize for Skip<LEN>` panics on fewer than `LEN` bytes. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (LEN : Usize) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ¬ misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ _ => True ⦄ := by
  unfold misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact IntAndMisc.not_spec_bind (io.ParseBuf.skip_panics buf LEN h)

/-- `MySerialize for Skip<LEN>`: appends `LEN` zero bytes. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : misc.raw.Skip LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ List.replicate LEN.val (byte 0) ⦄ := by
  unfold misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize
  step*
  simp [buf'_post, s_post, Array.repeat, byte]
  right; rfl

end mysql_common
