import Defs

/-! Statements for `impl From<io::Error> for PacketCodecError` (spec file: `Specs/Proto/Codec/Error.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<io::Error> for PacketCodecError`: wraps the error as `Io`. -/
theorem proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from_eq (e : core.io.error.Error) :
    proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from e = ok (.Io e) := by
  sorry

end mysql_common
