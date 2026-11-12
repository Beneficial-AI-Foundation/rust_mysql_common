import Defs

/-! Statements for `struct Skip<LEN> and its impls` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for Skip<LEN>`: `SIZE` is `Some(LEN)`. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN := by
  sorry

/-- `MyDeserialize for Skip<LEN>`: skips `LEN` bytes. Unchecked: panics on a shorter buffer; `parse` checks. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).isSome ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  sorry

/-- `MySerialize for Skip<LEN>`: appends `LEN` zero bytes. -/
theorem misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : misc.raw.Skip LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ List.replicate LEN.val (byte 0) ⦄ := by
  sorry

end mysql_common
