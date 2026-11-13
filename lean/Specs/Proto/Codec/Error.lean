import Proofs.Proto.Codec.Error.PacketCodecError

/-!
# `src/proto/codec/error.rs`
    The codec's error type `PacketCodecError` (`Io`, `PacketTooLarge`, `PacketsOutOfSync`,
    `BadCompressedPacketHeader`): its `From<io::Error>` conversion, used by `?` in the compressed
    codec.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** None.

    **Trusted axioms.** `core.io.error.Error` (an opaque type), nothing else.

    **Not covered.** `Display` and `std::error::Error::source` (formatting and trait objects,
    excluded from the translation).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl From<io::Error> for PacketCodecError` -/

/-- `From<io::Error> for PacketCodecError`: wraps the error as `Io`. -/
recall proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from_eq (e : core.io.error.Error) :
    proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from e = ok (.Io e)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms proto.codec.error.PacketCodecError.Insts.CoreConvertFromError.from_eq`
end mysql_common
