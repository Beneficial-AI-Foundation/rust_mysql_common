import Defs

/-! Statements for `impls for [u8; LEN]` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for [u8; LEN]`: `SIZE` is `Some(LEN)`. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN := by
  sorry

/-- `MyDeserialize for [u8; LEN]`: the next `LEN` bytes. Unchecked: panics on a shorter buffer; `parse` checks. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).map (·.val) = some (buf.val.take LEN.val) ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  sorry

/-- `MySerialize for [u8; LEN]`: appends the bytes. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : Array U8 LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ self.val ⦄ := by
  sorry

end mysql_common
