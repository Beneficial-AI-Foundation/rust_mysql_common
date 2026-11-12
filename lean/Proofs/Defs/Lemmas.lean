import Defs

/-! Sanity properties of the definitions in `Defs/` (pure Lean, no Rust): the decoders invert the
encoders. They are not spec statements, but reviewers can use them to check that the definitions
mean what they say. Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std

namespace Defs

/-- Little-endian bytes read back as the number mod `2^(8k)`. -/
theorem leNat_leBytes (k n : Nat) : leNat (leBytes k n) = n % 2 ^ (8 * k) := by
  sorry

/-- `leBytes k n` has `k` bytes. -/
theorem length_leBytes (k n : Nat) : (leBytes k n).length = k := by
  sorry

/-- Two's complement read back: `toSigned` inverts `leBytesI` on the representable range. -/
theorem toSigned_leNat_leBytesI (k : Nat) (x : Int) (hk : 0 < k)
    (hx : -2 ^ (8 * k - 1) ≤ x ∧ x < 2 ^ (8 * k - 1)) :
    toSigned (8 * k) (leNat (leBytesI k x)) = x := by
  sorry

/-- The protocol decoder reads back every length-encoded integer `n < 2^64`. -/
theorem lenencIntDecode_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    lenencIntDecode (lenencInt n ++ t) = some (n, t) := by
  sorry

/-- The crate's decoder agrees on well-formed input. -/
theorem checkedLenencInt_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    checkedLenencInt (lenencInt n ++ t) = (some n, t) := by
  sorry

/-- The crate's decoder reads back every length-encoded string. -/
theorem checkedLenencStr_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s ++ t) = (some s, t) := by
  sorry

/-- The size of a varlen encoding. -/
theorem varlenUint_length (n : Nat) : (varlenUint n).length = varlenUintSize n := by
  sorry

/-- The serialization-library decoder reads back every encoding of `n < 2^64`. -/
theorem varlenUintDecode_varlenUint (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    varlenUintDecode (varlenUint n ++ t) = some (n, t) := by
  sorry

/-- The JSONB reader reads back the JSONB encoding of every `n < 2^32`. -/
theorem jsonbVarLenRead_jsonbVarLen (n : Nat) (t : List U8) (hn : n < 2 ^ 32) :
    jsonbVarLenRead (jsonbVarLen n ++ t) = (some n, t) := by
  sorry

/-- The two encodings `BytesRepr for VarLen` mixes up disagree from 128 on: the JSONB reader does
    not read back a lenenc length `128 ≤ n < 251` (it continues into the following bytes, or fails
    at the end of input). -/
theorem jsonbVarLenRead_lenencInt_ne (n : Nat) (t : List U8) (hn : 128 ≤ n ∧ n < 251) :
    jsonbVarLenRead (lenencInt n ++ t) ≠ (some n, t) := by
  sorry

/-- The exact misreading: a lenenc length byte `128 ≤ n < 251` followed by a byte `b < 128` is
    read as the JSONB value `(n - 128) + 128 * b`, consuming both bytes. E.g. a 200-byte string
    starting with `'a'` (97) is read as having length 12488. -/
theorem jsonbVarLenRead_lenencInt_misread (n : Nat) (b : U8) (t : List U8)
    (hn : 128 ≤ n ∧ n < 251) (hb : b.val < 128) :
    jsonbVarLenRead (lenencInt n ++ b :: t) = (some (n - 128 + 128 * b.val), t) := by
  sorry

/-- The crate's lenient DATE/DATETIME/TIMESTAMP reader agrees with the protocol's format on the
    lengths the protocol defines (on a truncated input both fail; the crate's reader then has
    consumed the length byte). -/
theorem dateRead_dateProto (l : U8) (rest : List U8)
    (hl : l.val = 0 ∨ l.val = 4 ∨ l.val = 7 ∨ l.val = 11) :
    dateRead (l :: rest) =
      match dateProto (l :: rest) with
      | some (v, r) => (some v, r)
      | none => (none, rest) := by
  sorry

/-- The crate's lenient TIME reader agrees with the protocol's format on the lengths the protocol
    defines. (The protocol defines the sign byte only as 0 or 1; both readers take anything but 1
    as positive.) -/
theorem timeRead_timeProto (l : U8) (rest : List U8) (hl : l.val = 0 ∨ l.val = 8 ∨ l.val = 12) :
    timeRead (l :: rest) =
      match timeProto (l :: rest) with
      | some (v, r) => (some v, r)
      | none => (none, rest) := by
  sorry

/-- The binary decoder reads back every encoded value at a compatible column type, up to
    `binNorm`. -/
theorem binRead_binEnc (v : mysql_common.value.Value) (ct : mysql_common.constants.ColumnType)
    (u : Bool) (t : List U8) (hc : binCompatible (Val.ofValue v) ct) :
    binRead ct u (binEnc (Val.ofValue v) ++ t) = (some (binNorm u (Val.ofValue v)), t) := by
  sorry

/-- The text decoder reads a length-encoded string as `Bytes`. -/
theorem textRead_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    textRead (lenencStr s ++ t) = (some (.bytes s), t) := by
  sorry

end Defs
