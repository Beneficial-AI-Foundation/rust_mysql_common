import Defs
import Proofs.Defs.LemmasG
set_option autoImplicit false
open Aeneas Aeneas.Std Result mysql_common Defs
/-! Helper lemmas for the proofs of the stage g dependency conversions (chrono, time, uuid,
bigint, decimal, bigdecimal, json): `Proofs/Value/Convert/{Chrono,Time,Uuid,Bigint}/*`,
`Proofs/Value/Convert/{Decimal,Bigdecimal}.lean`, `Proofs/Value/Json/*`. -/

namespace mysql_common.ConvDeps

/-- `Trusted.u8sOf` of the UTF-8 bytes of a string is `utf8`. -/
theorem u8sOf_toUTF8 (s : String) : Trusted.u8sOf s.toUTF8 = utf8 s := by
  simp only [Trusted.u8sOf, utf8, byte]
  apply List.map_congr_left
  intro b _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- `String::into_bytes` in bounds: the vector of the string's UTF-8 bytes. -/
theorem string_into_bytes_val (s : String) (h : (utf8 s).length ≤ Usize.max) :
    ∃ v, value.convert.trusted.string_into_bytes s = ok v ∧ v.val = utf8 s := by
  have h' : (Trusted.u8sOf s.toUTF8).length ≤ Usize.max := by rw [u8sOf_toUTF8]; exact h
  refine ⟨alloc.vec.Vec.from _ h', ?_, ?_⟩
  · unfold value.convert.trusted.string_into_bytes; rw [dite_eq_left_of_eq_true (eq_true h')]
  · rw [alloc.vec.Vec.from_val, u8sOf_toUTF8]

open Classical in
/-- `str::from_utf8` agrees with `IsUtf8`. -/
theorem str_from_utf8_eq (b : Slice U8) :
    value.convert.trusted.str_from_utf8 b = ok (if IsUtf8 b.val then (some b : Option Str) else none) := by
  unfold value.convert.trusted.str_from_utf8
  by_cases h : IsUtf8 b.val
  · have h' := (Defs.isUtf8_iff_isValidUTF8 _).1 h; simp only [h, h', ite_true]
  · have h' : ¬ (Trusted.bytesOf b.val).IsValidUTF8 := fun h' => h ((Defs.isUtf8_iff_isValidUTF8 _).2 h')
    simp only [h, h', ite_false]

@[simp] theorem vec_deref_val {T : Type} (v : alloc.vec.Vec T) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- The ASCII hypothesis on a `Bytes` value, as the text parsers' precondition. -/
theorem bytesAscii_bytes {b : alloc.vec.Vec U8} (ha : (Val.ofValue (.Bytes b)).bytesAscii) :
    ∀ c ∈ (alloc.vec.Vec.deref b).val, c.val < 128 := by
  simpa [Val.ofValue, Val.bytesAscii] using ha

/-! ## Casts -/

theorem u16_hcast_i32_val (y : U16) : (UScalar.hcast .I32 y).val = y.val := by
  rw [UScalar.hcast_val_eq]
  have := y.hBounds
  apply Int.bmod_eq_of_le <;> scalar_tac

theorem u32_hcast_i32_val (y : U32) (h : y.val < 2 ^ 31) : (UScalar.hcast .I32 y).val = y.val := by
  rw [UScalar.hcast_val_eq]
  apply Int.bmod_eq_of_le <;> scalar_tac

theorem u8_into_u32_val (x : U8) : ∃ y, core.convert.IntoFrom.into core.convert.FromU32U8 x = ok y ∧ y.val = x.val := by
  simp [core.convert.IntoFrom.into]

/-- Binds that return: the first computation returned. -/
theorem bind_eq_ok_inv {α β : Type} {m : Result α} {k : α → Result β} {w : β}
    (h : (m >>= k) = ok w) : ∃ a, m = ok a ∧ k a = ok w := by
  cases m <;> simp_all

theorem daysInMonth_le (y : Int) (m : Nat) : Trusted.daysInMonth y m ≤ 31 := by
  unfold Trusted.daysInMonth
  split <;> (try split) <;> omega

/-! ## Panic messages -/

theorem bind_new_display {T β : Type} (inst : core.fmt.Display T) (x : T)
    (f : core.fmt.rt.Argument → Result β) :
    Std.bind (core.fmt.rt.Argument.new_display inst x) f = f () := by
  unfold core.fmt.rt.Argument.new_display; exact Std.bind_ok _ _

theorem bind_arguments_new {N M : Usize} {β : Type} (a : Std.Array U8 N)
    (b : Std.Array core.fmt.rt.Argument M) (f : core.fmt.Arguments → Result β) :
    Std.bind (core.fmt.Arguments.new a b) f = f () := by
  unfold core.fmt.Arguments.new; exact Std.bind_ok _ _

/-! ## Text literals -/

theorem digitsVal4_lt (a b c d : U8) : digitsVal [a, b, c, d] < 2 ^ 31 := by
  have := a.hBounds; have := b.hBounds; have := c.hBounds; have := d.hBounds
  simp [digitsVal] at *
  omega

theorem datetimeStringRead_year_lt (bs : List U8) (t : Nat × Nat × Nat × Nat × Nat × Nat × Nat)
    (h : datetimeStringRead bs = some t) : t.1 < 2 ^ 31 := by
  unfold datetimeStringRead at h
  split at h
  · split at h
    · split at h
      · cases h; exact digitsVal4_lt _ _ _ _
      · split at h
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact digitsVal4_lt _ _ _ _
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## `time::Month` -/

theorem month_from_u8_spec (mo : U8) : ∃ o, value.convert.trusted.time_month_from_u8 mo = ok o ∧
    (o.isSome ↔ 1 ≤ mo.val ∧ mo.val ≤ 12) ∧ ∀ m, o = some m → Trusted.monthNumber m = mo.val := by
  unfold value.convert.trusted.time_month_from_u8
  refine ⟨_, rfl, ?_⟩
  -- Every month arm is closed by `simp_all`; the out-of-range arm needs `omega`.
  split <;> simp_all [Trusted.monthNumber]
  omega

theorem month_to_u8_val (m : time.month.Month) : ∃ u, value.convert.trusted.time_month_to_u8 m = ok u ∧
    u.val = Trusted.monthNumber m := by
  cases m <;> simp [value.convert.trusted.time_month_to_u8, Trusted.monthNumber]

/-! ## `from_value_opt` from `try_from` -/

/-- The committed result of a `try_from` producing a `ParseIr`. -/
def mapIr {T E : Type} : core.result.Result (value.convert.ParseIr T) E → core.result.Result T E
  | .Ok p => .Ok p.1
  | .Err e => .Err e

@[simp] theorem mapIr_ok {T E : Type} (x : T) (w : value.Value) :
    (mapIr (.Ok ((x, w) : value.convert.ParseIr T)) : core.result.Result T E) = .Ok x := rfl
@[simp] theorem mapIr_err {T E : Type} (e : E) :
    (mapIr (T := T) (.Err e) : core.result.Result T E) = .Err e := rfl

/-! The parts of a `try_from` spec carried over to its committed result `mapIr r`. -/

theorem mapIr_okPart {T E : Type} {e : E} {r : core.result.Result (value.convert.ParseIr T) E}
    (h : okPart r = none → r = .Err e) : okPart (mapIr r) = none → mapIr r = .Err e := by
  cases r with
  | Ok p => simp [okPart, mapIr]
  | Err e' => intro; rw [h rfl]; rfl

theorem mapIr_isOk {T E : Type} {P : Prop} {r : core.result.Result (value.convert.ParseIr T) E}
    (h : (∃ p, r = .Ok p) ↔ P) : (∃ x, mapIr r = .Ok x) ↔ P := by
  rw [← h]
  cases r <;> simp [mapIr]

theorem mapIr_ok_of {T E : Type} {w₀ : value.Value} {Q : T → Prop}
    {r : core.result.Result (value.convert.ParseIr T) E}
    (h : ∀ x w, r = .Ok (x, w) → w = w₀ ∧ Q x) : ∀ x, mapIr r = .Ok x → Q x := by
  intro x hx
  cases r with
  | Ok p => obtain ⟨x0, w⟩ := p; cases hx; exact (h x0 w rfl).2
  | Err e => cases hx

theorem mapIr_err_of {T E : Type} {e : E} {r : core.result.Result (value.convert.ParseIr T) E}
    (h : r = .Err e) : mapIr r = .Err e := by
  rw [h]; rfl

theorem spec_eq_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ v, m = ok v ∧ P v := by
  cases m <;> simp_all

theorem from_value_opt_eq_of {T : Type} (inst : value.convert.FromValue T (value.convert.ParseIr T))
    (hd : inst.from_value_opt = value.convert.FromValue.from_value_opt.default inst)
    (hinto : ∀ p, inst.coreconvertIntoInst.into p = ok p.1) (v : value.Value) {r}
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok r) :
    value.convert.from_value_opt inst v = ok (mapIr r) := by
  simp only [value.convert.from_value_opt, hd, value.convert.FromValue.from_value_opt.default, h]
  cases r with
  | Ok p => simp [hinto, mapIr]
  | Err e => simp [mapIr]

theorem from_value_opt_spec_of {T : Type} (inst : value.convert.FromValue T (value.convert.ParseIr T))
    (hd : inst.from_value_opt = value.convert.FromValue.from_value_opt.default inst)
    (hinto : ∀ p, inst.coreconvertIntoInst.into p = ok p.1) (v : value.Value) {P : _ → Prop}
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v ⦃ P ⦄) :
    value.convert.from_value_opt inst v ⦃ r' => ∃ r, P r ∧ r' = mapIr r ⦄ := by
  obtain ⟨r, hr, hp⟩ := spec_eq_ok h
  rw [from_value_opt_eq_of inst hd hinto v hr, WP.spec_ok]
  exact ⟨r, hp, rfl⟩

end mysql_common.ConvDeps
