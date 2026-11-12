import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impls for f64` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for f64`: `SIZE` is `Some(8)`. -/
theorem F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 8#usize := by
  unfold F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for f64`: the double whose bit pattern is the next 8 bytes, little-endian. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
theorem F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  unfold F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.eat_f64_le_spec buf h as ⟨ x, rest, hx, hr ⟩
  simp [okPart, hx, hr]

/-- `MyDeserialize for f64` panics on fewer than 8 bytes. -/
theorem F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ _ => True ⦄ := by
  unfold F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  intro hc
  exact io.ParseBuf.eat_f64_le_panics buf h (spec_of_bind _ _ _ hc)

/-- `MySerialize for f64`: appends the bit pattern, little-endian. -/
theorem F64.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : F64) (buf : alloc.vec.Vec U8) (h : buf.length + 8 ≤ Usize.max) :
    F64.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 self.bits.val ⦄ := by
  unfold F64.Insts.Mysql_commonProtoMySerialize.serialize alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_f64_le
  simp only [core.f64.F64.to_bits]
  step with IntAndMisc.put_u64_le_spec buf self.bits h as ⟨ v, hv ⟩
  exact hv

end mysql_common
