import Defs
import Proofs.Util.ConvBytesTime

/-! Facts about the stage g definitions (spec file: `Specs/DefsG.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The readable definition of UTF-8 validity (`IsUtf8`: the encoding of some string) agrees with
    the check the trusted model of `str::from_utf8` uses (Lean's `ByteArray.IsValidUTF8`). -/
theorem isUtf8_iff_isValidUTF8 (bs : List U8) :
    IsUtf8 bs ↔ (Trusted.bytesOf bs).IsValidUTF8 := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [mysql_common.CBTUtil.bytesOf_utf8]; exact s.isValidUTF8
  · intro h
    exact ⟨_, mysql_common.CBTUtil.utf8_ofByteArray bs h⟩

end Defs
