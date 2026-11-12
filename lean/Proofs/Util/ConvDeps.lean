import Defs
import Proofs.Defs.LemmasG
set_option autoImplicit false
open Aeneas Aeneas.Std Result mysql_common Defs
/-! Helper lemmas for the proofs of the stage g dependency conversions (chrono, time, uuid,
bigint, decimal, bigdecimal, json): `Proofs/Value/Convert/{Chrono,Time,Uuid,Bigint}/*`,
`Proofs/Value/Convert/{Decimal,Bigdecimal}.lean`, `Proofs/Value/Json/*`. -/

namespace mysql_common.ConvDeps

/-- `Trusted.u8sOf` of the UTF-8 bytes of a string is `utf8`. -/
theorem u8sOf_toUTF8 (s : String) : Trusted.u8sOf s.toUTF8 = utf8 s := by
  simp only [Trusted.u8sOf, utf8, byte]
  apply List.map_congr_left
  intro b _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- `String::into_bytes` in bounds: the vector of the string's UTF-8 bytes. -/
theorem string_into_bytes_val (s : String) (h : (utf8 s).length ≤ Usize.max) :
    ∃ v, value.convert.trusted.string_into_bytes s = ok v ∧ v.val = utf8 s := by
  have h' : (Trusted.u8sOf s.toUTF8).length ≤ Usize.max := by rw [u8sOf_toUTF8]; exact h
  refine ⟨alloc.vec.Vec.from _ h', ?_, ?_⟩
  · unfold value.convert.trusted.string_into_bytes; rw [dite_eq_left_of_eq_true (eq_true h')]
  · rw [alloc.vec.Vec.from_val, u8sOf_toUTF8]

open Classical in
/-- `str::from_utf8` agrees with `IsUtf8`. -/
theorem str_from_utf8_eq (b : Slice U8) :
    value.convert.trusted.str_from_utf8 b = ok (if IsUtf8 b.val then (some b : Option Str) else none) := by
  unfold value.convert.trusted.str_from_utf8
  by_cases h : IsUtf8 b.val
  · have h' := (Defs.isUtf8_iff_isValidUTF8 _).1 h; simp only [h, h', ite_true]
  · have h' : ¬ (Trusted.bytesOf b.val).IsValidUTF8 := fun h' => h ((Defs.isUtf8_iff_isValidUTF8 _).2 h')
    simp only [h, h', ite_false]

@[simp] theorem vec_deref_val {T : Type} (v : alloc.vec.Vec T) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

end mysql_common.ConvDeps
