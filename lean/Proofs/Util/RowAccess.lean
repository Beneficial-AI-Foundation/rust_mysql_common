import Defs

/-! Helper lemmas for the proofs of the `RowAccess` group (`Proofs/Row/*.lean`, the non-tuple
`FromRow` impls, `Proofs/Defs/LemmasRowConvert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.RowAccessUtil

theorem spec_eq_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ v, m = ok v ∧ P v := by
  cases m <;> simp_all

/-- Binds that return: the first computation returned. -/
theorem bind_eq_ok_inv {α β : Type} {m : Result α} {k : α → Result β} {w : β}
    (h : (m >>= k) = ok w) : ∃ a, m = ok a ∧ k a = ok w := by
  cases m <;> simp_all

/-- `Vec<u8>::clone` is the identity. -/
theorem vec_u8_clone_eq (v : alloc.vec.Vec U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v := by
  obtain ⟨s, hs, hv⟩ := spec_eq_ok
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := v.slice) (by intros; rfl))
  simp [alloc.vec.CloneVec.clone, hs, ← hv]

/-- `Value::clone` is the identity. -/
theorem value_clone_eq (v : value.Value) : value.Value.Insts.CoreCloneClone.clone v = ok v := by
  cases v <;> simp [value.Value.Insts.CoreCloneClone.clone, lift, F32.Insts.CoreCloneClone.clone,
    F64.Insts.CoreCloneClone.clone, vec_u8_clone_eq]

@[simp] theorem vec_deref_val {T : Type} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

@[simp] theorem vec_deref_getElem? {T : Type} (v : alloc.vec.Vec T) (i : Usize) :
    (alloc.vec.Vec.deref v)[i]? = v.val[i.val]? := by
  rw [Slice.getElem?_Usize_eq, vec_deref_val]

theorem list_set_opt_some {T : Type} (l : List T) (i : Nat) (x : T) :
    l.set_opt i (some x) = l.set i x := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih => cases i <;> simp [List.set_opt, ih]

theorem list_set_opt_none {T : Type} (l : List T) (i : Nat) : l.set_opt i none = l := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih => cases i <;> simp [List.set_opt, ih]

theorem vec_slice_getElem? {T : Type} (v : alloc.vec.Vec T) (i : Usize) :
    v.slice[i]? = v.val[i.val]? := rfl

/-- Writing back through `get_mut` a cell after `Option::take`. -/
theorem vec_mk_set_opt {T : Type} (v : alloc.vec.Vec (Option T)) (i : Usize) :
    ({ slice := v.slice.set_opt i (some none) } : alloc.vec.Vec (Option T)) = v.set i none := by
  apply alloc.vec.Vec.ext
  show (v.slice.set_opt i (some none)).val = (v.set i none).val
  simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val, Slice.set_opt_val_eq, list_set_opt_some]
  rfl

/-- Writing back an empty cell through `get_mut` leaves the vector unchanged. -/
theorem vec_mk_set_opt_self {T : Type} (v : alloc.vec.Vec (Option T)) (i : Usize)
    (h : v.val[i.val]? = some none) :
    ({ slice := v.slice.set_opt i (some none) } : alloc.vec.Vec (Option T)) = v := by
  apply alloc.vec.Vec.ext
  have h' : v.slice.val[i.val]? = some none := h
  simp only [alloc.vec.Vec.val, Slice.set_opt_val_eq, list_set_opt_some]
  apply List.ext_getElem?; intro j
  rw [List.getElem?_set]; split_ifs with hj <;> simp_all

/-- Writing back nothing through `get_mut` leaves the vector unchanged. -/
theorem vec_mk_set_opt_none {T : Type} (v : alloc.vec.Vec T) (i : Usize) :
    ({ slice := v.slice.set_opt i none } : alloc.vec.Vec T) = v := by
  apply alloc.vec.Vec.ext
  simp only [alloc.vec.Vec.val, Slice.set_opt_val_eq, list_set_opt_none]

theorem allCells_some_iff {α : Type} (cells : List (Option α)) (vs : List α) :
    allCells cells = some vs ↔ cells = vs.map some := by
  induction cells generalizing vs with
  | nil => cases vs <;> simp [allCells]
  | cons c cs ih =>
    cases c with
    | none => cases vs <;> simp [allCells]
    | some v =>
      cases vs with
      | nil => simp [allCells]
      | cons w ws => simp [allCells, ih, eq_comm, and_comm]

/-- `FromValue for Value::from_value` is the identity. -/
theorem value_from_value_eq (v : value.Value) :
    value.Value.Insts.Mysql_commonValueConvertFromValueValueIr.from_value v = ok v := by
  simp [value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from,
    core.convert.IntoFrom.into, value.Value.Insts.CoreConvertFromValueIr.from]

end mysql_common.RowAccessUtil
