import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.RawBytesSeq
import Proofs.Binlog.Consts.StatusVarKey

/-! Statements for `struct StatusVarsIterator and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(bytes)`: at position 0. -/
theorem binlog.events.query_event.StatusVarsIterator.new_spec (s : Slice U8) :
    binlog.events.query_event.StatusVarsIterator.new s = ok { pos := 0#usize, status_vars := s } := by
  rfl

namespace SVIter

theorem hasNul_cons (b : U8) (l : List U8) : hasNul (b :: l) = (b.val == 0 || hasNul l) := by
  simp [hasNul]

theorem get_usize (s : Slice U8) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice U8) s i = ok (s.val[i.val]?) := rfl

/-- `skip_db_name`: the position after the `0`-terminated name at `pos + total`. -/
theorem skip_db_name_spec (it : binlog.events.query_event.StatusVarsIterator) : ∀ (m : Nat) (total : Usize),
    it.status_vars.length - (it.pos.val + total.val) = m → it.pos.val + total.val ≤ it.status_vars.length + 1 →
    it.status_vars.length + 2 ^ 16 ≤ Usize.max →
    binlog.events.query_event.StatusVarsIterator.skip_db_name it total ⦃ o => o.map (·.val) =
      (if hasNul (it.status_vars.val.drop (it.pos.val + total.val)) then
        some (total.val + (beforeZero (it.status_vars.val.drop (it.pos.val + total.val))).length + 1) else none) ⦄ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro total hm hpt hmax
    unfold binlog.events.query_event.StatusVarsIterator.skip_db_name
    step as ⟨i, hi⟩
    rw [get_usize]
    simp only [bind_ok]
    cases hx : it.status_vars.val[i.val]? with
    | none =>
      have hge : it.status_vars.val.length ≤ i.val := by
        rw [List.getElem?_eq_none_iff] at hx; exact hx
      have hd : it.status_vars.val.drop (it.pos.val + total.val) = [] := by
        apply List.drop_eq_nil_of_le; omega
      simp [hd, hasNul]
    | some x =>
      have hlt : i.val < it.status_vars.val.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
      have hd : it.status_vars.val.drop (it.pos.val + total.val) = x :: it.status_vars.val.drop (i.val + 1) := by
        rw [show it.pos.val + total.val = i.val by omega, List.drop_eq_getElem_cons hlt]
        rw [List.getElem?_eq_getElem hlt] at hx
        simp only [Option.some.injEq] at hx
        rw [hx]
      simp only [hd]
      by_cases hx0 : x = 0#u8
      · subst hx0
        simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
        step as ⟨t1, ht1⟩
        simp [hasNul_cons, mysql_common.beforeZero_cons, ht1]
      · have hxv : x.val ≠ 0 := fun h => hx0 (UScalar.eq_of_val_eq (by simpa using h))
        have hne : (x != 0#u8) = true := by simpa using hx0
        simp only [hne, ite_true]
        step as ⟨t1, ht1⟩
        have hslen : it.status_vars.length = it.status_vars.val.length := rfl
        apply WP.spec_mono (ih (it.status_vars.length - (it.pos.val + t1.val)) (by omega) t1 rfl (by omega) hmax)
        intro o ho
        rw [ho]
        have hd' : it.pos.val + t1.val = i.val + 1 := by omega
        rw [hd']
        by_cases hn : hasNul (it.status_vars.val.drop (i.val + 1)) = true
        · simp [hasNul_cons, mysql_common.beforeZero_cons, hxv, hn, ht1]; omega
        · simp [hasNul_cons, hxv, hn]

end SVIter

/-- `Iterator::next`: the next variable of the walk from the current position (`svStep`; nothing at or past the end), and the position after it; `None` at an unknown key, a truncated value, or the end (the position after a `None` is not stated: the iterator is not fused). The length bound: status variables come from a query event, whose length field is a u16, so real blocks have at most 65535 bytes. -/
theorem binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next_spec (it : binlog.events.query_event.StatusVarsIterator)
    (hlen : it.status_vars.length + 2 ^ 16 ≤ Usize.max) :
    binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next it ⦃ o it' =>
      match svStep it.status_vars.val it.pos.val with
      | some (kv, p) => o.map (fun x => (statusVarKeyCode x.key, x.value.val)) = some kv ∧ it'.pos.val = p ∧ it'.status_vars = it.status_vars
      | none => o = none ∧ it'.status_vars = it.status_vars ⦄ := by
  sorry

end mysql_common
