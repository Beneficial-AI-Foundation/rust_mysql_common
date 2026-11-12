import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impls for [u8; LEN]` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for [u8; LEN]`: `SIZE` is `Some(LEN)`. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN := by
  unfold ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for [u8; LEN]`: the next `LEN` bytes. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).map (·.val) = some (buf.val.take LEN.val) ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  unfold ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.eat_spec buf LEN h as ⟨ v, rest, hv, hr ⟩
  step*
  simp_all [okPart, Array.from_slice]

/-- `MyDeserialize for [u8; LEN]` panics on fewer than `LEN` bytes. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (LEN : Usize) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ¬ ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ _ => True ⦄ := by
  unfold ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  intro hc
  exact io.ParseBuf.eat_panics buf LEN h (spec_of_bind _ _ _ hc)

/-- `MySerialize for [u8; LEN]`: appends the bytes. -/
theorem ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : Array U8 LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ self.val ⦄ := by
  unfold ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index]
  step with put_slice_spec buf self.to_slice (by simpa using h) as ⟨ v, hv ⟩
  simp [hv]

end mysql_common
