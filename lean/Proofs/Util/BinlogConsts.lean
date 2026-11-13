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

/-- The value of a scalar literal (as it appears in a `match` on `k#uscalar`). -/
theorem uscalar_mk_val {ty : UScalarTy} (b : BitVec ty.numBits) : (UScalar.mk b).val = b.toNat :=
  rfl

/-- `u8::try_from(u64)` followed by `unwrap`, for a value that fits. -/
theorem u8_tryFrom_u64_unwrap_lt {α : Type} (v : U64) (h : v.val < 256) (k : U8 → Result α) :
    (do
      let r ← U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from v
      let i ← core.result.Result.unwrap core.num.error.TryFromIntError.Insts.CoreFmtDebug r
      k i) = k (byte v.val) := by
  have h' : v.val ≤ U8.max := by rw [U8.max_eq]; omega
  have hc : UScalar.cast .U8 v = byte v.val := by
    apply UScalar.eq_of_val_eq
    simp [UScalar.cast_val_eq, byte, uscalar_mk_val]
  simp only [U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from, core.num.tryFromUScalar,
    UScalar.max_UScalarTy_U8_eq, h', ↓reduceIte, bind_ok, core.result.Result.unwrap, hc]

/-- `u8::try_from(u64)` followed by `unwrap` panics for a value that does not fit. -/
theorem u8_tryFrom_u64_unwrap_ge {α : Type} (v : U64) (h : 256 ≤ v.val)
    (k : U8 → Result α) :
    (do
      let r ← U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from v
      let i ← core.result.Result.unwrap core.num.error.TryFromIntError.Insts.CoreFmtDebug r
      k i) = fail .panic := by
  have h' : ¬ v.val ≤ U8.max := by rw [U8.max_eq]; omega
  simp only [U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from, core.num.tryFromUScalar,
    UScalar.max_UScalarTy_U8_eq, h', ↓reduceIte, bind_ok, core.result.Result.unwrap, bind_fail]

end mysql_common.BinlogConstsUtil
