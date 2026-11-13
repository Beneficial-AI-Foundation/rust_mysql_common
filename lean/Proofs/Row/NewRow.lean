import Defs
import Proofs.Util.RowAccess

/-! Statements for `fn new_row` (spec file: `Specs/Row.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open RowAccessUtil

private theorem values_to_cells_loop_spec (vs : List value.Value) (values : alloc.vec.Vec value.Value)
    (cells : alloc.vec.Vec (Option value.Value)) (i : Usize)
    (hlen : values.length = vs.length) (hi : i.val ≤ vs.length)
    (hc : cells.val = (vs.take i.val).map some)
    (hd : values.val.drop i.val = vs.drop i.val) :
    row.values_to_cells_loop values cells i ⦃ r => r.val = vs.map some ⦄ := by
  unfold row.values_to_cells_loop
  apply loop.spec_decr_nat (fun p : _ × _ × Usize => vs.length - p.2.2.val)
    (fun p => p.1.length = vs.length ∧ p.2.2.val ≤ vs.length ∧
      p.2.1.val = (vs.take p.2.2.val).map some ∧ p.1.val.drop p.2.2.val = vs.drop p.2.2.val)
  · clear hlen hi hc hd values cells i
    rintro ⟨values, cells, i⟩ ⟨hlen, hi, hc, hd⟩
    simp only at hlen hi hc hd
    unfold row.values_to_cells_loop.body
    simp only [alloc.vec.Vec.index_mut_slice_index]
    have hcl : cells.val.length = i.val := by rw [hc]; simp; omega
    step*
    · have hlt : i.val < vs.length := by scalar_tac
      have hvi : values.val[i.val]? = some vs[i.val] := by
        have := congrArg (·[0]?) hd
        simpa [List.getElem?_drop, List.getElem?_eq_getElem hlt] using this
      have hv : v = vs[i.val] := by
        rw [v_post]; simp [List.getElem?_eq_some_iff] at hvi; exact hvi.2
      refine ⟨by simp_all, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp_all [List.take_add_one]
      · rw [index_mut_back_post]
        simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val, i2_post]
        rw [List.drop_set_of_lt (by omega)]
        have := congrArg (List.drop 1) hd
        simpa [List.drop_drop, Nat.add_comm] using this
    · have : i.val = vs.length := by scalar_tac
      rw [hc, this, List.take_length]
  · exact ⟨hlen, hi, hc, hd⟩

/-- `new_row`: the row of the given values (every cell present) and columns, when there are as
    many of each. -/
theorem row.new_row_spec (values : alloc.vec.Vec value.Value) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length = columns.length) :
    row.new_row values columns ⦃ r => r.values.val = values.val.map some ∧ r.columns = columns ⦄ := by
  unfold row.new_row row.values_to_cells
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
  have hm : alloc.vec.Vec.len values = Slice.len columns := by scalar_tac
  simp only [massert, hm, ↓reduceIte, bind_ok]
  apply WP.spec_bind (values_to_cells_loop_spec values.val values _ 0#usize rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) (by simp))
  intro r hr
  simp [hr]

/-- `new_row` panics (`assert!`) when the numbers of values and columns differ. -/
theorem row.new_row_panics (values : alloc.vec.Vec value.Value) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length ≠ columns.length) :
    row.new_row values columns = fail .assertionFailure := by
  unfold row.new_row
  have hm : ¬ alloc.vec.Vec.len values = Slice.len columns := by
    intro he; apply h; scalar_tac
  simp [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, massert, hm]

end mysql_common
