import Proofs.Defs.LemmasG

/-!
# Facts about the stage g definitions (`formal/specs/Defs/Convert.lean`)

Pure-Lean properties of the definitions used by `Specs/Value/Convert*.lean` and
`Specs/Value/Json/SerdeIntegration.lean`. A signer should read them: the specs state UTF-8
validity with the readable `IsUtf8` (the bytes are the UTF-8 encoding of some string), while the
trusted model of `str::from_utf8` (`FunsExternal.lean`) checks `ByteArray.IsValidUTF8`; this
bridge says the two agree. Proofs: `Proofs/Defs/LemmasG.lean`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The readable definition of UTF-8 validity (`IsUtf8`: the encoding of some string) agrees with
    the check the trusted model of `str::from_utf8` uses (Lean's `ByteArray.IsValidUTF8`). -/
recall isUtf8_iff_isValidUTF8 (bs : List U8) :
    IsUtf8 bs ↔ (Trusted.bytesOf bs).IsValidUTF8

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.isUtf8_iff_isValidUTF8
end Defs
