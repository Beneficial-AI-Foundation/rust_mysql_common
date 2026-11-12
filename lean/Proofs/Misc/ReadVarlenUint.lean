import Defs

/-! Statements for `fn read_varlen_uint` (spec file: `Specs/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `read_varlen_uint`: total; the serialization-library decoder `varlenUintDecode`. On error
    (empty or truncated input) the buffer is unchanged. -/
theorem misc.read_varlen_uint_spec (buf : io.ParseBuf) :
    misc.read_varlen_uint buf ⦃ r rest =>
      (okPart r).map (fun n => (n.val, rest.val)) = varlenUintDecode buf.val ∧
      (okPart r = none → rest = buf) ⦄ := by
  sorry

/-- Round trip: `read_varlen_uint` reads back `varlenUint v` (what `write_varlen_uint` writes), for every `v : u64`. -/
theorem misc.read_varlen_uint_roundtrip (v : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = varlenUint v.val ++ tail) :
    misc.read_varlen_uint buf ⦃ r rest => okPart r = some v ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
