import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl TryFrom<Value> for ParseIr<Uuid>, fn uuid_from_slice` (spec file: `Specs/Value/Convert/Uuid.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `uuid_from_slice` (`Uuid::from_slice(b).ok()`): total; the uuid with these bytes exactly
    when there are 16 of them. -/
theorem value.convert.uuid.uuid_from_slice_spec (b : Slice U8) :
    value.convert.uuid.uuid_from_slice b ⦃ r => ∀ u : uuid.Uuid, r = some u ↔ Array.val u = b.val ⦄ := by
  unfold value.convert.uuid.uuid_from_slice
  have hu : ∀ u : uuid.Uuid, (Array.val u).length = 16 := fun u => by simp
  by_cases h : b.val.length = 16
  · have hl : Slice.len b = 16#usize := by
      apply UScalar.eq_of_val_eq; simpa [Slice.len] using h
    simp only [hl, bne_self_eq_false, Bool.false_eq_true, ite_false]
    step*
    subst s1_post to_slice_mut_back_post
    simp [uuid.builder.Uuid.from_bytes]
    intro u
    constructor
    · rintro rfl; simp [h]
    · intro hv; apply Std.Array.ext; simp [h, hv]
  · have hl : Slice.len b ≠ 16#usize := by
      intro he; apply h; have := congrArg UScalar.val he; simpa [Slice.len] using this
    simp only [bne_iff_ne, ne_eq, hl, not_false_eq_true, ite_true, WP.spec_ok]
    intro u
    simp only [reduceCtorEq, false_iff]
    intro hv; apply h; rw [← hv, hu]

/-- `TryFrom<Value> for ParseIr<Uuid>`: total; succeeds exactly on `Bytes` of length 16, keeping
    the original value for `rollback`. -/
theorem value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ u w, r = .Ok (u, w) ↔ w = v ∧ Val.ofValue v = .bytes (Array.val u)) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  cases v <;> simp [value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, Val.ofValue]
  case Bytes bs =>
    apply WP.spec_bind (value.convert.uuid.uuid_from_slice_spec _)
    intro r hr
    cases r with
    | none =>
      simp only [WP.spec_ok, reduceCtorEq, false_iff, imp_self, and_true]
      intro u w ⟨_, hb⟩
      have := (hr u).2 (by simp [hb])
      simp at this
    | some u =>
      simp only [WP.spec_ok, reduceCtorEq, imp_self, and_true]
      intro u' w
      have h1 := (hr u').1
      have h2 := (hr u').2
      simp only [ConvDeps.vec_deref_val, Option.some.injEq] at h1 h2
      constructor
      · intro he
        cases he
        exact ⟨rfl, (h1 rfl).symm⟩
      · rintro ⟨rfl, hb⟩
        rw [h2 hb.symm]

/-- `from_value_opt::<Uuid>`: as `try_from`, committed. -/
theorem uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid v ⦃ r =>
      (∀ u, r = .Ok u ↔ Val.ofValue v = .bytes (Array.val u)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v))
  rintro _ ⟨r, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun u => ?_, ConvDeps.mapIr_okPart h2⟩
  rw [← (h1 u v).trans (and_iff_right rfl)]
  cases r with
  | Ok p =>
    obtain ⟨u', w⟩ := p
    obtain ⟨rfl, -⟩ := (h1 u' w).1 rfl
    exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  | Err e => simp [ConvDeps.mapIr]

/-- `From<ParseIr<Uuid>> for Uuid` is `commit`, `From<ParseIr<Uuid>> for Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrUuid.from_eq (x : uuid.Uuid) (w : value.Value) :
    uuid.Uuid.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

end mysql_common
