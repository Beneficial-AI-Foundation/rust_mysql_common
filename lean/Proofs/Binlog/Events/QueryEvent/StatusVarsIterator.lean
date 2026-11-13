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

/-- `db_names_len`: `count` names from `pos + total` (`dbNamesLen`), plus `total`. -/
theorem db_names_len_spec (it : binlog.events.query_event.StatusVarsIterator) : ∀ (c : Nat) (count total : Usize), count.val = c →
    it.pos.val + total.val ≤ it.status_vars.length + 1 → it.status_vars.length + 2 ^ 16 ≤ Usize.max →
    binlog.events.query_event.StatusVarsIterator.db_names_len it count total ⦃ o => o.map (·.val) =
      (dbNamesLen c (it.status_vars.val.drop (it.pos.val + total.val))).map (total.val + ·) ⦄ := by
  intro c
  induction c with
  | zero =>
    intro count total hc _ _
    unfold binlog.events.query_event.StatusVarsIterator.db_names_len
    have : count = 0#usize := UScalar.eq_of_val_eq (by simpa using hc)
    simp [this, dbNamesLen]
  | succ c ih =>
    intro count total hc hpt hmax
    unfold binlog.events.query_event.StatusVarsIterator.db_names_len
    have hne : count ≠ 0#usize := fun h => by subst h; simp at hc
    simp only [hne, ite_false]
    step with skip_db_name_spec it _ total rfl hpt hmax as ⟨o, ho⟩
    cases hn : hasNul (it.status_vars.val.drop (it.pos.val + total.val)) with
    | false =>
      simp only [hn, Bool.false_eq_true, ite_false] at ho
      cases o with
      | some _ => simp at ho
      | none => simp [dbNamesLen, hn]
    | true =>
      simp only [hn, ite_true] at ho
      cases o with
      | none => simp at ho
      | some t1 =>
        simp only [Option.map_some, Option.some.injEq] at ho
        simp only []
        step as ⟨c1, hc1⟩
        have hex : ∃ b ∈ it.status_vars.val.drop (it.pos.val + total.val), b.val = 0 := by
          simpa [hasNul] using hn
        have hbl := mysql_common.beforeZero_length_lt _ hex
        have hslen : it.status_vars.length = it.status_vars.val.length := rfl
        have hdl : (it.status_vars.val.drop (it.pos.val + total.val)).length = it.status_vars.val.length - (it.pos.val + total.val) := by simp
        apply WP.spec_mono (ih c1 t1 (by omega) (by omega) hmax)
        intro o' ho'
        rw [ho']
        have hd : it.status_vars.val.drop (it.pos.val + t1.val) =
            (it.status_vars.val.drop (it.pos.val + total.val)).drop
              ((beforeZero (it.status_vars.val.drop (it.pos.val + total.val))).length + 1) := by
          rw [List.drop_drop]; congr 1; omega
        rw [hd]
        simp only [dbNamesLen, hn, ite_true, Option.map_map]
        congr 1; funext y; simp only [Function.comp]; omega

theorem var_len_spec (it : binlog.events.query_event.StatusVarsIterator) (suffix : Usize) (hs : suffix.val ≤ 1) :
    binlog.events.query_event.StatusVarsIterator.var_len it suffix ⦃ o => o.map (·.val) =
      (it.status_vars.val.drop it.pos.val).head?.map (fun b => 1 + b.val + suffix.val) ⦄ := by
  unfold binlog.events.query_event.StatusVarsIterator.var_len
  rw [get_usize]
  simp only [bind_ok, List.head?_drop]
  cases hx : it.status_vars.val[it.pos.val]? with
  | none => simp
  | some x =>
    simp only [lift, bind_ok]
    have hc : (UScalar.cast .Usize x).val = x.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
    step*
    simp_all

set_option linter.unusedSimpArgs false in
theorem value_len_spec (it : binlog.events.query_event.StatusVarsIterator) (key : binlog.consts.StatusVarKey)
    (hp : it.pos.val ≤ it.status_vars.length) (hmax : it.status_vars.length + 2 ^ 16 ≤ Usize.max) :
    binlog.events.query_event.StatusVarsIterator.value_len it key ⦃ o => o.map (·.val) =
      svValueLen (statusVarKeyCode key) (it.status_vars.val.drop it.pos.val) ⦄ := by
  have hslen : it.status_vars.length = it.status_vars.val.length := rfl
  cases key
  case Flags2 =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case SqlMode =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case Catalog =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    apply WP.spec_mono (var_len_spec it 1#usize (by decide))
    intro o ho; rw [ho]; simp only [statusVarKeyCode, svValueLen, ↓reduceIte]; rfl
  case AutoIncrement =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case Charset =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case TimeZone =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    apply WP.spec_mono (var_len_spec it 0#usize (by decide))
    intro o ho; rw [ho]; simp only [statusVarKeyCode, svValueLen, ↓reduceIte]; simp
  case CatalogNz =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    apply WP.spec_mono (var_len_spec it 0#usize (by decide))
    intro o ho; rw [ho]; simp only [statusVarKeyCode, svValueLen, ↓reduceIte]; simp
  case LcTimeNames =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case CharsetDatabase =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case TableMapForUpdate =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case MasterDataWritten =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case Invoker =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    rw [get_usize]
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp only [bind_ok]
    cases hx : it.status_vars.val[it.pos.val]? with
    | none =>
      have : it.status_vars.val.drop it.pos.val = [] := by
        rw [List.getElem?_eq_none_iff] at hx; exact List.drop_eq_nil_of_le hx
      simp [this]
    | some x =>
      have hlt : it.pos.val < it.status_vars.val.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
      have hd : it.status_vars.val.drop it.pos.val = x :: it.status_vars.val.drop (it.pos.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt]; rw [List.getElem?_eq_getElem hlt] at hx; simp only [Option.some.injEq] at hx; rw [hx]
      simp only [lift, bind_ok, hd, List.head?_cons, Option.some.injEq]
      have hc : (UScalar.cast .Usize x).val = x.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      rw [get_usize]
      simp only [bind_ok]
      have hdrop : (List.drop (1 + x.val) (x :: it.status_vars.val.drop (it.pos.val + 1))).head? = it.status_vars.val[i1.val]? := by
        rw [Nat.add_comm 1, List.drop_succ_cons, List.head?_drop, List.getElem?_drop]
        congr 1; omega
      rw [hdrop]
      cases hy : it.status_vars.val[i1.val]? with
      | none => simp
      | some y =>
        simp only [lift, bind_ok]
        have hcy : (UScalar.cast .Usize y).val = y.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
        step*
        simp_all
  case UpdatedDbNames =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    rw [get_usize]
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp only [bind_ok]
    cases hx : it.status_vars.val[it.pos.val]? with
    | none =>
      have : it.status_vars.val.drop it.pos.val = [] := by
        rw [List.getElem?_eq_none_iff] at hx; exact List.drop_eq_nil_of_le hx
      simp [this]
    | some x =>
      have hlt : it.pos.val < it.status_vars.val.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
      have hd : it.status_vars.val.drop it.pos.val = x :: it.status_vars.val.drop (it.pos.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt]; rw [List.getElem?_eq_getElem hlt] at hx; simp only [Option.some.injEq] at hx; rw [hx]
      simp only [lift, bind_ok, hd]
      have hc : (UScalar.cast .Usize x).val = x.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
      apply WP.spec_mono (db_names_len_spec it x.val _ 1#usize hc (by simp; omega) hmax)
      intro o ho; rw [ho]; rfl
  case Microseconds =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case CommitTs =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case CommitTs2 =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case ExplicitDefaultsForTimestamp =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case DdlLoggedWithXid =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case DefaultCollationForUtf8mb4 =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case SqlRequirePrimaryKey =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp
  case DefaultTableEncryption =>
    unfold binlog.events.query_event.StatusVarsIterator.value_len
    simp only [statusVarKeyCode, svValueLen, ↓reduceIte]
    simp

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
