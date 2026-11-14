import Defs
import Proofs.Util.ParamsAsSql

/-! Statements for `fn escaped` (private; used by `Value::as_sql`) (spec file:
`Specs/Value/AsSql.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `escaped(s, nbe)`: exactly the MySQL quoting `quoteSql nbe` of the bytes of `s`. (A Rust
    `&str` is always valid UTF-8; for a `Str` that is not, the final `from_utf8` would fail and
    this panics, which cannot happen from Rust.) The output must fit in a `Vec` (`hlen`): past
    `usize::MAX` bytes the push fails (capacity overflow), as everywhere in `Specs/Io.lean`. -/
theorem value.escaped_spec (s : Str) (nbe : Bool) (h : IsUtf8 s.val)
    (hlen : (quoteSql nbe s.val).length ≤ Usize.max) :
    value.escaped s nbe ⦃ r => utf8 r = quoteSql nbe s.val ⦄ := by
  obtain ⟨t, ht⟩ := PASUtil.isUtf8_quoteSql nbe s.val h
  rw [PASUtil.quoteSql_eq] at hlen ht
  simp only [List.length_cons, List.length_append] at hlen
  unfold value.escaped
  step with (show value.convert.trusted.str_as_bytes s ⦃ b => b.val = s.val ⦄ from
    (WP.spec_ok _).mpr rfl) as ⟨b, hb⟩
  rw [← hb] at hlen ht
  step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity U8 (Slice.len b)) 39#u8 (by unfold alloc.vec.Vec.with_capacity; simp; scalar_tac) as ⟨o1, ho1⟩
  have hw : (alloc.vec.Vec.with_capacity U8 (Slice.len b)).val = [] := by
    unfold alloc.vec.Vec.with_capacity; simp
  rw [hw, List.nil_append] at ho1
  simp only [List.length_nil, Nat.zero_add] at hlen
  cases nbe
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with PASUtil.escaped_loop1_spec b b.length o1 0#usize (by simp) (by simp)
      (by rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero]; simp only [alloc.vec.Vec.length, ho1, List.length_singleton]; omega) as ⟨o2, ho2⟩
    step with alloc.vec.Vec.push_spec o2 39#u8 (by rw [ho2, ho1, List.drop_zero]; simp only [List.length_append, List.length_singleton]; omega) as ⟨o3, ho3⟩
    have hq : o3.val = utf8 t := by rw [ht, ho3, ho2, ho1]; simp; rfl
    simp only [value.convert.trusted.string_from_utf8, hq, CBTUtil.fromUTF8?_utf8, Std.bind_ok,
      WP.spec_ok]
    rw [ht, PASUtil.quoteSql_eq, ← hb]
  · simp only [↓reduceIte]
    step with PASUtil.escaped_loop0_spec b b.length o1 0#usize (by simp) (by simp)
      (by rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero]; simp only [alloc.vec.Vec.length, ho1, List.length_singleton]; omega) as ⟨o2, ho2⟩
    step with alloc.vec.Vec.push_spec o2 39#u8 (by rw [ho2, ho1, List.drop_zero]; simp only [List.length_append, List.length_singleton]; omega) as ⟨o3, ho3⟩
    have hq : o3.val = utf8 t := by rw [ht, ho3, ho2, ho1]; simp; rfl
    simp only [value.convert.trusted.string_from_utf8, hq, CBTUtil.fromUTF8?_utf8, Std.bind_ok,
      WP.spec_ok]
    rw [ht, PASUtil.quoteSql_eq, ← hb]

end mysql_common
