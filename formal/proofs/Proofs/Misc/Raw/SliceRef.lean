import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `impl MyDeserialize for &[u8]` (spec file: `Specs/Misc/Raw.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `SIZE` is `None`. -/
theorem SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE = none := by
  unfold SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE; rfl

/-- total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. -/
theorem SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (len : Usize) (buf : io.ParseBuf) :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize
  step with io.ParseBuf.checked_eat_spec buf len as ⟨ o, buf1, ho ⟩
  split at ho
  · obtain ⟨ho1, ho2⟩ := ho
    cases o with
    | none => simp at ho1
    | some x => simp at ho1; simp [okPart, *]
  · obtain ⟨ho1, ho2⟩ := ho
    subst ho1 ho2
    simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, *]

end mysql_common
