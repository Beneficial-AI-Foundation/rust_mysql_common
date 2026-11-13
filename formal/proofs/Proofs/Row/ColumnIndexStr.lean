import Defs
import Proofs.Util.RowAccess
import Proofs.Packets.Column

/-! Statements for `impl ColumnIndex for &str` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem slice_u8_eq_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ (b : Bool) => b ↔ (s1.val = s2.val) ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ ?_)
  · intro b hb; rw [hb, Slice.eq_iff]
  · intro x y; simp

private theorem column_idx_by_name_spec (nm : Slice U8) (cols : Slice packets.Column) (k : Nat) (i : Usize)
    (hk : cols.length - i.val = k) (hi : i.val ≤ cols.length) :
    row.column_idx_by_name nm cols i ⦃ o => o.map (·.val) =
      ((cols.val.drop i.val).findIdx? (fun c => decide (colName c = nm.val))).map (· + i.val) ⦄ := by
  induction k generalizing i with
  | zero =>
    rw [row.column_idx_by_name]
    have : ¬ i < cols.len := by scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok]
    rw [List.drop_of_length_le (by simp at hk ⊢; omega)]; simp
  | succ k ih =>
    rw [row.column_idx_by_name]
    have hlt : i < cols.len := by scalar_tac
    have hlt' : i.val < cols.val.length := by scalar_tac
    simp only [hlt, ↓reduceIte]
    rw [List.drop_eq_getElem_cons hlt', List.findIdx?_cons]
    step with Slice.index_usize_spec as ⟨c, hc⟩
    step with packets.Column.name_ref_spec as ⟨s, hs⟩
    step with slice_u8_eq_spec as ⟨b, hb⟩
    split
    · simp_all [colName]
    · step as ⟨i2, hi2⟩
      apply WP.spec_mono (ih i2 (by scalar_tac) (by scalar_tac))
      intro o ho
      rw [ho]
      have hb' : ¬ colName cols.val[i.val] = nm.val := by simp_all [colName]
      simp [hb', hi2, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- `ColumnIndex for &str`: the position of the first column named exactly `self` (byte for
    byte, case-sensitive), or `None`. Never panics. -/
theorem Shared0Str.Insts.Mysql_commonRowColumnIndex.idx_spec (self : Str) (columns : Slice packets.Column) :
    Shared0Str.Insts.Mysql_commonRowColumnIndex.idx self columns ⦃ o =>
      o.map (·.val) = colIndexByName self.val columns.val ⦄ := by
  unfold Shared0Str.Insts.Mysql_commonRowColumnIndex.idx value.convert.trusted.str_as_bytes
  refine WP.spec_bind (Pₘ := fun s => s = self) ((WP.spec_ok _).mpr rfl) ?_
  rintro s rfl
  apply WP.spec_mono (column_idx_by_name_spec s columns _ 0#usize rfl (by simp))
  intro o ho
  simpa [colIndexByName] using ho

end mysql_common
