import Defs

/-! Statements for `impls for f64` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for f64`: `SIZE` is `Some(8)`. -/
theorem F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 8#usize := by
  sorry

/-- `MyDeserialize for f64`: the double whose bit pattern is the next 8 bytes, little-endian. Unchecked: panics on a shorter buffer; `parse` checks. -/
theorem F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  sorry

/-- `MySerialize for f64`: appends the bit pattern, little-endian. -/
theorem F64.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : F64) (buf : alloc.vec.Vec U8) (h : buf.length + 8 ≤ Usize.max) :
    F64.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 self.bits.val ⦄ := by
  sorry

end mysql_common
