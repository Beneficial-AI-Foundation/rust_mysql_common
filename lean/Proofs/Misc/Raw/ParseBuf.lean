import Defs
import Proofs.Util.ParseBuf

/-! Statements for `impl MyDeserialize for ParseBuf` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `SIZE` is `None`. -/
theorem io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq :
    io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE = none := by
  simp [io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE]

/-- total; the given number `len` of bytes as a sub-buffer, an error with the buffer unchanged if there are fewer. -/
theorem io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (len : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  exact deserialize_usize_ok len buf

end mysql_common
