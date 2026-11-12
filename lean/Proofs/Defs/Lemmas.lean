import Proofs.Util.IntAndMisc
import Proofs.Util.ParseBuf

/-! Sanity properties of the definitions in `Defs/` (pure Lean, no Rust): the decoders invert the
encoders. They are not spec statements, but reviewers can use them to check that the definitions
mean what they say. -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- Little-endian bytes read back as the number mod `2^(8k)`. -/
theorem leNat_leBytes (k n : Nat) : leNat (leBytes k n) = n % 2 ^ (8 * k) := by
  exact IntAndMisc.leNat_leBytes' k n

/-- `leBytes k n` has `k` bytes. -/
theorem length_leBytes (k n : Nat) : (leBytes k n).length = k := by
  exact IntAndMisc.length_leBytes' k n

/-- Two's complement read back: `toSigned` inverts `leBytesI` on the representable range. -/
theorem toSigned_leNat_leBytesI (k : Nat) (x : Int) (hk : 0 < k)
    (hx : -2 ^ (8 * k - 1) ≤ x ∧ x < 2 ^ (8 * k - 1)) :
    toSigned (8 * k) (leNat (leBytesI k x)) = x := by
  rw [IntAndMisc.leNat_leBytesI]
  exact IntAndMisc.toSigned_emod (8 * k) (by omega) x hx.1 hx.2

/-- The protocol decoder reads back every length-encoded integer `n < 2^64`. -/
theorem lenencIntDecode_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    lenencIntDecode (lenencInt n ++ t) = some (n, t) := by
  unfold lenencInt
  split_ifs with h1 h2 h3
  · simp [lenencIntDecode, PBUtil.byte_val, Nat.mod_eq_of_lt (by omega : n < 256)]
    omega
  · simp [lenencIntDecode, PBUtil.byte_val, PBUtil.readLE_leBytes 2 n t (by omega)]
  · simp [lenencIntDecode, PBUtil.byte_val, PBUtil.readLE_leBytes 3 n t (by omega)]
  · simp [lenencIntDecode, PBUtil.byte_val, PBUtil.readLE_leBytes 8 n t (by omega)]

/-- The crate's decoder agrees on well-formed input. -/
theorem checkedLenencInt_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    checkedLenencInt (lenencInt n ++ t) = (some n, t) := by
  exact PBUtil.checkedLenencInt_lenencInt n t hn

/-- The crate's decoder reads back every length-encoded string. -/
theorem checkedLenencStr_lenencStr (s t : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s ++ t) = (some s, t) := by
  unfold lenencStr checkedLenencStr
  rw [List.append_assoc, PBUtil.checkedLenencInt_lenencInt _ _ hs]
  simp

/-- The size of a varlen encoding. -/
theorem varlenUint_length (n : Nat) : (varlenUint n).length = varlenUintSize n := by
  exact IntAndMisc.varlenUint_length' n

/-- The serialization-library decoder reads back every encoding of `n < 2^64`. -/
theorem varlenUintDecode_varlenUint (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    varlenUintDecode (varlenUint n ++ t) = some (n, t) := by
  exact IntAndMisc.varlenUintDecode_varlenUint' n t hn

/-- The JSONB reader reads back the JSONB encoding of every `n < 2^32`. -/
theorem jsonbVarLenRead_jsonbVarLen (n : Nat) (t : List U8) (hn : n < 2 ^ 32) :
    jsonbVarLenRead (jsonbVarLen n ++ t) = (some n, t) := by
  exact IntAndMisc.jsonbVarLenRead_jsonbVarLen' n t hn

/-- The two encodings `BytesRepr for VarLen` mixes up disagree from 128 on: the JSONB reader does
    not read back a lenenc length `128 ≤ n < 251` (it continues into the following bytes, or fails
    at the end of input). -/
theorem jsonbVarLenRead_lenencInt_ne (n : Nat) (t : List U8) (hn : 128 ≤ n ∧ n < 251) :
    jsonbVarLenRead (lenencInt n ++ t) ≠ (some n, t) := by
  have hl : lenencInt n = [byte n] := by simp [lenencInt, show n < 251 by omega]
  have hb : (byte n).val = n := by rw [PBUtil.byte_val]; omega
  rw [hl]
  unfold jsonbVarLenRead
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.findIdx?_cons, hb,
    show ¬ n < 128 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
  cases h : List.findIdx? (fun b => decide (b.val < 128)) (List.take 4 t) with
  | none => simp
  | some j =>
    simp only [Option.map_some, ne_eq, Prod.mk.injEq, not_and]
    intro _ hd
    rw [List.findIdx?_eq_some_iff_findIdx_eq] at h
    have hj : j < t.length := by have := h.1; simp at this; omega
    have := congrArg List.length hd
    simp at this
    omega

/-- The exact misreading: a lenenc length byte `128 ≤ n < 251` followed by a byte `b < 128` is
    read as the JSONB value `(n - 128) + 128 * b`, consuming both bytes. E.g. a 200-byte string
    starting with `'a'` (97) is read as having length 12488. -/
theorem jsonbVarLenRead_lenencInt_misread (n : Nat) (b : U8) (t : List U8)
    (hn : 128 ≤ n ∧ n < 251) (hb : b.val < 128) :
    jsonbVarLenRead (lenencInt n ++ b :: t) = (some (n - 128 + 128 * b.val), t) := by
  have hl : lenencInt n = [byte n] := by simp [lenencInt, show n < 251 by omega]
  have hbn : (byte n).val = n := by rw [PBUtil.byte_val]; omega
  rw [hl]
  have := IntAndMisc.jsonbVarLenRead_some ([byte n] ++ b :: t) 1 (by norm_num)
    (by intro c hc; simp at hc; subst hc; omega) b t (by simp) hb
  rw [this]
  simp only [List.singleton_append, List.take_succ_cons, List.take_zero, base128, hbn, pow_one]
  have hv : n % 128 + 128 * 0 + 128 * (b.val % 128) = n - 128 + 128 * b.val := by omega
  rw [hv, if_pos (by omega)]

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
    defines, when the sign byte (if there is one) is 0 or 1, the only values the protocol defines.
    (On any other sign byte the protocol decoder is `none`, while the crate reads it as
    positive.) -/
theorem timeRead_timeProto (l : U8) (rest : List U8) (hl : l.val = 0 ∨ l.val = 8 ∨ l.val = 12)
    (hsign : l.val ≠ 0 → ∀ n ∈ rest.head?, n.val ≤ 1) :
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
  have hb : ∃ b r, lenencStr s ++ t = b :: r ∧ b.val ≠ 0xFB := by
    unfold lenencStr lenencInt
    split_ifs with h1 h2 h3
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
  obtain ⟨b, r, hbr, hne⟩ := hb
  have hc := checkedLenencStr_lenencStr s t hs
  rw [hbr] at hc ⊢
  simp [textRead, hne, hc]

end Defs
