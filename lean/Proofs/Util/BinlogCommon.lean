import Defs
import Proofs.Util.ParseBuf

/-! Small lemmas shared by the binlog event helper files (`Util/BinlogEvHdr`, `Util/BinlogEvGtid`,
`Util/BinlogEvRows`): little-endian bytes, `byte`, saturating `usize` arithmetic, length-encoded
integer lengths and the `Default` steps of zero-sized raw fields. The helper files re-export them
under their own namespaces. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogCommon

theorem leNat_leBytes_lt (k n : Nat) (h : n < 2 ^ (8 * k)) : leNat (leBytes k n) = n := by
  rw [PBUtil.leNat_leBytes, Nat.mod_eq_of_lt h]

theorem byte_val_self (x : U8) : byte x.val = x := by
  unfold byte; cases x; simp [UScalar.val]

theorem sat_sub_usize (x y : Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  have hb : x.val - y.val < 2 ^ UScalarTy.Usize.numBits := lt_of_le_of_lt (Nat.sub_le _ _) x.hBounds
  show (UScalar.saturating_sub x y).val = _
  simp only [UScalar.saturating_sub, Nat.zero_max]
  exact Nat.mod_eq_of_lt hb

theorem usize_saturating_add_val (x y : Usize) :
    (core.num.Usize.saturating_add x y).val = min (x.val + y.val) Usize.max := by
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.max_USize_eq]
  rw [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · omega
  · have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      rw [Usize.max_def]; simp [Usize.numBits]
    omega

theorem u32_max_le_usize : 2 ^ 32 - 1 ≤ Usize.max := by
  rw [Usize.max_def]; simp only [Usize.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

theorem lenencInt_length_le (n : Nat) : (lenencInt n).length ≤ 9 := by
  unfold lenencInt; split_ifs <;> simp [PBUtil.length_leBytes]

@[step] theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]

@[step] theorem skip_default_spec (L : Usize) :
    misc.raw.Skip.Insts.CoreDefaultDefault.default L ⦃ _ => True ⦄ := by
  simp [misc.raw.Skip.Insts.CoreDefaultDefault.default]

end mysql_common.BinlogCommon
