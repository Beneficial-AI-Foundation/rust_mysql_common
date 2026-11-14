import Defs
import Proofs.Util.Constants

/-! Helper lemmas for the `Proofs/Binlog/{Consts,Mod,Row}/*` proofs. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogConstsUtil

export _root_.mysql_common.ConstUtil (uscalar_eq_iff nat_or_eq_iff_and_eq uscalar_val_not u16_val_not)

theorem u8_val_not (x : U8) : (~~~x).val = 2 ^ 8 - 1 - x.val := uscalar_val_not x

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
