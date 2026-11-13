import Defs

/-! Helper lemmas for the `Proofs/Constants/*` proofs (flag words and column types). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.ConstUtil

/-- Scalars are equal iff their values are. -/
theorem uscalar_eq_iff {ty : UScalarTy} (x y : UScalar ty) : x = y ↔ x.val = y.val :=
  ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

/-- `a | x = x` iff `a & x = a` (both say: the bits of `a` are bits of `x`). -/
theorem nat_or_eq_iff_and_eq (a x : Nat) : a ||| x = x ↔ a &&& x = a := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    have hi := congrArg (Nat.testBit · i) h <;>
    simp only [Nat.testBit_or, Nat.testBit_and] at hi ⊢ <;>
    cases ha : a.testBit i <;> cases hx : x.testBit i <;> simp_all

/-- The value of a bitwise negation. -/
theorem uscalar_val_not {ty : UScalarTy} (x : UScalar ty) :
    (~~~x).val = 2 ^ ty.numBits - 1 - x.val := by
  simp only [UScalar.val, UScalar.bv_not, BitVec.toNat_not]

theorem u16_val_not (x : U16) : (~~~x).val = 2 ^ 16 - 1 - x.val := uscalar_val_not x

theorem u32_val_not (x : U32) : (~~~x).val = 2 ^ 32 - 1 - x.val := uscalar_val_not x

/-- `StatusFlags::all()` evaluates to `0xFFFB`. -/
theorem statusFlags_all_eq : constants.StatusFlags.all = ok (65531#u16) := by
  simp only [constants.StatusFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

/-- `CapabilityFlags::all()` evaluates to `0xFFFF_FFFF`. -/
theorem capabilityFlags_all_eq : constants.CapabilityFlags.all = ok (4294967295#u32) := by
  simp only [constants.CapabilityFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

/-- `ColumnFlags::all()` evaluates to `0xFFFF`. -/
theorem columnFlags_all_eq : constants.ColumnFlags.all = ok (65535#u16) := by
  simp only [constants.ColumnFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

end mysql_common.ConstUtil
