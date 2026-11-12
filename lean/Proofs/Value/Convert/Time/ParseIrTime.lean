import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl TryFrom<Value> for ParseIr<Time>` (spec file: `Specs/Value/Convert/Time.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<Time>` on a non-negative (sign flag false) `TIME` with 0 days: total; converts exactly
    when time accepts the fields. -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time (h m s : U8) (us : U32) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Time false 0#u32 h m s us ∧ timeTime x = (h.val, m.val, s.val, us.val) ⦄ := by
  obtain ⟨r, hr, hiff, hfld⟩ := Trusted.timeFromHmsMicro_spec h m s us
  simp [value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.trusted.time_time_from_hms_micro, hr]
  split
  · cases r with
    | none =>
      simp [okPart, timeTimeValid] at hiff ⊢
      omega
    | some x =>
      obtain ⟨h1, h2, h3, h4⟩ := hfld x rfl
      simp only [Option.isSome_some, true_iff] at hiff
      simp only [WP.spec_ok, timeTimeValid]
      refine ⟨fun h => by simp [okPart] at h, ⟨fun _ => hiff, fun _ => ⟨_, rfl⟩⟩, fun x1 w he => ?_⟩
      cases he
      simp [timeTime, h1, h2, h3, h4]
  · rename_i hne; exact absurd rfl hne

/-- `TryFrom<Value> for ParseIr<Time>` on `Bytes`: not valid UTF-8 or fewer than 8 bytes is an
    error; 8 bytes: time's `hh:mm:ss` parser; more: the parser with a fraction (both opaque). -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if b.val.length < 8 then .Err (.TryFromParsed .InsufficientInformation)
          else if b.val.length = 8 then Trusted.timeParseTime (alloc.vec.Vec.deref b)
          else Trusted.timeParseTimeMicro (alloc.vec.Vec.deref b)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  simp only [value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.time.parse_mysql_time_string_with_time, ConvDeps.str_from_utf8_eq]
  by_cases hu : IsUtf8 b.val
  · simp only [ConvDeps.vec_deref_val, hu, ite_true]
    simp [value.convert.trusted.str_as_bytes, value.convert.trusted.time_parse_insufficient_information,
      value.convert.trusted.time_time_parse_time, value.convert.trusted.time_time_parse_time_micro]
    simp only [lift]
    rcases Nat.lt_trichotomy b.val.length 8 with hl | hl | hl
    · simp [hl, Nat.compare_eq_lt.mpr hl]
    · simp [hl]
      cases Trusted.timeParseTime b.deref <;> simp
    · simp [Nat.compare_eq_gt.mpr hl, show ¬ b.val.length < 8 by omega, show b.val.length ≠ 8 by omega]
      cases Trusted.timeParseTimeMicro b.deref <;> simp
  · simp [hu, value.convert.trusted.time_parse_insufficient_information]

/-- `TryFrom<Value> for ParseIr<Time>`: any other value (including a negative `TIME` or one with
    days) is an error. -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  cases v with
  | Time b i h m s us =>
    cases b
    · by_cases hi : i = 0#u32
      · subst hi; exact absurd rfl (hv h m s us)
      · simp only [value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from,
          Bool.false_eq_true, ite_false]
        split
        · exact absurd rfl hi
        · rfl
    · simp [value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from]
  | Bytes b => exact absurd rfl (hb b)
  | _ => simp [value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from]

/-- `from_value_opt`: as `try_from_time` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_time (h m s : U8) (us : U32) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x, r = .Ok x → timeTime x = (h.val, m.val, s.val, us.val) ⦄ := by
  apply WP.spec_mono (ConvDeps.from_value_opt_spec_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time h m s us))
  rintro r' ⟨r, ⟨h1, h2, h3⟩, rfl⟩
  cases r with
  | Ok p =>
    obtain ⟨x, w⟩ := p
    refine ⟨by simp [okPart], ?_, ?_⟩
    · simp only [ConvDeps.mapIr_ok]; exact ⟨fun _ => h2.1 ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · intro x' hx; cases hx; exact (h3 x w rfl).2
  | Err e =>
    have := h1 (by simp [okPart]); cases this
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · simp only [ConvDeps.mapIr_err]; constructor
      · rintro ⟨_, hp⟩; cases hp
      · intro hv; obtain ⟨_, hp⟩ := h2.2 hv; cases hp
    · intro x hx; cases hx

/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if b.val.length < 8 then .Err (.TryFromParsed .InsufficientInformation)
          else if b.val.length = 8 then Trusted.timeParseTime (alloc.vec.Vec.deref b)
          else Trusted.timeParseTimeMicro (alloc.vec.Vec.deref b)) with
        | .Ok x => .Ok x
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes b)]
  split <;> [split <;> simp [ConvDeps.mapIr]; simp [ConvDeps.mapIr]]

/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime.from_value_opt_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.time.Time.Insts.Mysql_commonValueConvertFromValueParseIrTime v = ok (.Err v) := by
  rw [ConvDeps.from_value_opt_eq_of _ rfl (fun _ => rfl) _
    (value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other v hv hb)]
  rfl

end mysql_common
