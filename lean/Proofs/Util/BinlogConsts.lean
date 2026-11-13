import Defs

/-! Helper lemmas for the `Proofs/Binlog/{Consts,Mod,Row}/*` proofs. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogConstsUtil

/-- Scalars are equal iff their values are. -/
theorem uscalar_eq_iff {ty : UScalarTy} (x y : UScalar ty) : x = y ↔ x.val = y.val :=
  ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

/-- `a | x = x` iff `a & x = a`. -/
theorem nat_or_eq_iff_and_eq (a x : Nat) : a ||| x = x ↔ a &&& x = a := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    have hi := congrArg (Nat.testBit · i) h <;>
    simp only [Nat.testBit_or, Nat.testBit_and] at hi ⊢ <;>
    cases ha : a.testBit i <;> cases hx : x.testBit i <;> simp_all

theorem uscalar_val_not {ty : UScalarTy} (x : UScalar ty) :
    (~~~x).val = 2 ^ ty.numBits - 1 - x.val := by
  simp only [UScalar.val, UScalar.bv_not, BitVec.toNat_not]

theorem u8_val_not (x : U8) : (~~~x).val = 2 ^ 8 - 1 - x.val := uscalar_val_not x

theorem u16_val_not (x : U16) : (~~~x).val = 2 ^ 16 - 1 - x.val := uscalar_val_not x

theorem eventFlags_all_eq : binlog.consts.EventFlags.all = ok (1023#u16) := by
  simp only [binlog.consts.EventFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

theorem rowsEventFlags_all_eq : binlog.consts.RowsEventFlags.all = ok (15#u16) := by
  simp only [binlog.consts.RowsEventFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

theorem semiSyncFlags_all_eq : binlog.consts.SemiSyncFlags.all = ok (1#u8) := by
  simp only [binlog.consts.SemiSyncFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

theorem gtidFlags_all_eq : binlog.consts.GtidFlags.all = ok (1#u8) := by
  simp only [binlog.consts.GtidFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

theorem userVarFlags_all_eq : binlog.consts.UserVarFlags.all = ok (1#u8) := by
  simp only [binlog.consts.UserVarFlags.all, lift, bind_ok, ok.injEq]
  apply UScalar.eq_of_val_eq
  simp

end mysql_common.BinlogConstsUtil
