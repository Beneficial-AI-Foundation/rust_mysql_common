import Proofs.Defs.Lemmas

/-!
# Facts about the definitions (`lean/Defs/`)

Pure-Lean properties of the definitions the spec statements use. A signer should read them: they
check that the encoders and decoders in `Defs/` are inverse to each other, that the crate's
lenient temporal readers (`dateRead`, `timeRead`) agree with the protocol's formats
(`dateProto`, `timeProto`) on the lengths the protocol defines, and they pin down the
`BytesRepr for VarLen` format mismatch (`jsonbVarLenRead_lenencInt_ne`,
`jsonbVarLenRead_lenencInt_misread`). Proofs: `Proofs/Defs/Lemmas.lean`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std

namespace Defs

/-- Little-endian bytes read back as the number mod `2^(8k)`. -/
recall leNat_leBytes (k n : Nat) : leNat (leBytes k n) = n % 2 ^ (8 * k)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.leNat_leBytes
/-- `leBytes k n` has `k` bytes. -/
recall length_leBytes (k n : Nat) : (leBytes k n).length = k

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.length_leBytes
/-- Two's complement read back: `toSigned` inverts `leBytesI` on the representable range. -/
recall toSigned_leNat_leBytesI (k : Nat) (x : Int) (hk : 0 < k)
    (hx : -2 ^ (8 * k - 1) ≤ x ∧ x < 2 ^ (8 * k - 1)) :
    toSigned (8 * k) (leNat (leBytesI k x)) = x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.toSigned_leNat_leBytesI
/-- The protocol decoder reads back every length-encoded integer `n < 2^64`. -/
recall lenencIntDecode_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    lenencIntDecode (lenencInt n ++ t) = some (n, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.lenencIntDecode_lenencInt
/-- The crate's decoder agrees on well-formed input. -/
recall checkedLenencInt_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    checkedLenencInt (lenencInt n ++ t) = (some n, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.checkedLenencInt_lenencInt
/-- The crate's decoder reads back every length-encoded string. -/
recall checkedLenencStr_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s ++ t) = (some s, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.checkedLenencStr_lenencStr
/-- The size of a varlen encoding. -/
recall varlenUint_length (n : Nat) : (varlenUint n).length = varlenUintSize n

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.varlenUint_length
/-- The serialization-library decoder reads back every encoding of `n < 2^64`. -/
recall varlenUintDecode_varlenUint (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    varlenUintDecode (varlenUint n ++ t) = some (n, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.varlenUintDecode_varlenUint
/-- The JSONB reader reads back the JSONB encoding of every `n < 2^32`. -/
recall jsonbVarLenRead_jsonbVarLen (n : Nat) (t : List U8) (hn : n < 2 ^ 32) :
    jsonbVarLenRead (jsonbVarLen n ++ t) = (some n, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.jsonbVarLenRead_jsonbVarLen
/-- The two encodings `BytesRepr for VarLen` mixes up disagree from 128 on: the JSONB reader does
    not read back a lenenc length `128 ≤ n < 251` (it continues into the following bytes, or fails
    at the end of input). -/
recall jsonbVarLenRead_lenencInt_ne (n : Nat) (t : List U8) (hn : 128 ≤ n ∧ n < 251) :
    jsonbVarLenRead (lenencInt n ++ t) ≠ (some n, t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.jsonbVarLenRead_lenencInt_ne
/-- The exact misreading: a lenenc length byte `128 ≤ n < 251` followed by a byte `b < 128` is
    read as the JSONB value `(n - 128) + 128 * b`, consuming both bytes. E.g. a 200-byte string
    starting with `'a'` (97) is read as having length 12488. -/
recall jsonbVarLenRead_lenencInt_misread (n : Nat) (b : U8) (t : List U8)
    (hn : 128 ≤ n ∧ n < 251) (hb : b.val < 128) :
    jsonbVarLenRead (lenencInt n ++ b :: t) = (some (n - 128 + 128 * b.val), t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.jsonbVarLenRead_lenencInt_misread
/-- The crate's lenient DATE/DATETIME/TIMESTAMP reader agrees with the protocol's format on the
    lengths the protocol defines (on a truncated input both fail; the crate's reader then has
    consumed the length byte). -/
recall dateRead_dateProto (l : U8) (rest : List U8)
    (hl : l.val = 0 ∨ l.val = 4 ∨ l.val = 7 ∨ l.val = 11) :
    dateRead (l :: rest) =
      match dateProto (l :: rest) with
      | some (v, r) => (some v, r)
      | none => (none, rest)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.dateRead_dateProto
/-- The crate's lenient TIME reader agrees with the protocol's format on the lengths the protocol
    defines, when the sign byte (if there is one) is 0 or 1, the only values the protocol defines.
    (On any other sign byte the protocol decoder is `none`, while the crate reads it as
    positive.) -/
recall timeRead_timeProto (l : U8) (rest : List U8) (hl : l.val = 0 ∨ l.val = 8 ∨ l.val = 12)
    (hsign : l.val ≠ 0 → ∀ n ∈ rest.head?, n.val ≤ 1) :
    timeRead (l :: rest) =
      match timeProto (l :: rest) with
      | some (v, r) => (some v, r)
      | none => (none, rest)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.timeRead_timeProto
/-- The binary decoder reads back every encoded value at a compatible column type, up to
    `binNorm`. -/
recall binRead_binEnc (v : mysql_common.value.Value) (ct : mysql_common.constants.ColumnType)
    (u : Bool) (t : List U8) (hc : binCompatible (Val.ofValue v) ct) :
    binRead ct u (binEnc (Val.ofValue v) ++ t) = (some (binNorm u (Val.ofValue v)), t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.binRead_binEnc
/-- The text decoder reads a length-encoded string as `Bytes`. -/
recall textRead_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    textRead (lenencStr s ++ t) = (some (.bytes s), t)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.textRead_lenencStr
end Defs
