import Defs

/-! Statements for `impl MyDeserialize for &[u8]` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `SIZE` is `None`. -/
theorem SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE = none := by
  sorry

/-- total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. -/
theorem SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (len : Usize) (buf : io.ParseBuf) :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

end mysql_common
