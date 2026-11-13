import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Io.ParseBuf

/-! Statements for `struct StatusVar and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

private theorem slice_get_to (s : Slice U8) (n : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) s { «end» := n } ⦃ o =>
      if n.val ≤ s.val.length then ∃ t, o = some t ∧ t.val = s.val.take n.val else o = none ⦄ := by
  simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeToUsizeSlice.get]
  by_cases h : n.val ≤ s.val.length
  · have h' : n.val ≤ s.length := h
    simp only [h', ite_true]
    exact (WP.spec_ok _).mpr ⟨_, rfl, by simp [Slice.from_val, List.slice]⟩
  · have h' : ¬ n.val ≤ s.length := h
    simp only [h', ite_false]
    exact (WP.spec_ok _).mpr rfl

private theorem rawbytes_new_borrowed {T : Type} (inst : misc.raw.bytes.BytesRepr T Unit) (t : Slice U8) :
    misc.raw.bytes.RawBytes.new inst (core.convert.IntoFrom
      (alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice core.clone.CloneU8)) t ⦃ r => cowList r.1 = t.val ⦄ := by
  rw [misc.raw.bytes.RawBytes.new_eq inst _ t (.Borrowed t) rfl]
  exact (WP.spec_ok _).mpr rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- `get_value`: the value decoded per its key (`svValRead`); the raw value as the error if it is too short. (`Q_UPDATED_DB_NAMES` and `Q_MICROSECONDS`: see below.) -/
theorem binlog.events.query_event.StatusVar.get_value_spec (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key ≠ 12 ∧ statusVarKeyCode v.key ≠ 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match r with
      | .Ok x => svValRead (statusVarKeyCode v.key) v.value.val = some (svValView x)
      | .Err e => svValRead (statusVarKeyCode v.key) v.value.val = none ∧ e = v.value ⦄ := by
  obtain ⟨k, val⟩ := v
  cases k
  case Flags2 =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u32_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case SqlMode =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u64_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case Catalog =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    exact (WP.spec_ok _).mpr (by simp [svValRead, svValView, statusVarKeyCode])
  case AutoIncrement =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, r1, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, hr1⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only []
        step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o2, r2, ho2⟩
        split_ifs at ho2 with hl2
        · obtain ⟨h2, -⟩ := ho2
          cases o2 with
          | none => simp at h2
          | some y =>
            simp only [Option.map_some, Option.some.injEq] at h2
            simp only []
            simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
            simp only [Slice.length, hr1] at hl hl2 h2
            have : 4 ≤ val.val.length := by simp at hl2; omega
            simp [this, h1, h2]
        · obtain ⟨rfl, -⟩ := ho2
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          simp only [Slice.length, hr1] at hl hl2
          have : ¬ 4 ≤ val.val.length := by simp at hl2; omega
          simp [this]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      have : ¬ 4 ≤ val.val.length := by omega
      simp [this]
  case Charset =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, r1, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, hr1⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only []
        step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o2, r2, ho2⟩
        split_ifs at ho2 with hl2
        · obtain ⟨h2, hr2⟩ := ho2
          cases o2 with
          | none => simp at h2
          | some y =>
            simp only [Option.map_some, Option.some.injEq] at h2
            simp only []
            step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o3, r3, ho3⟩
            split_ifs at ho3 with hl3
            · obtain ⟨h3, -⟩ := ho3
              cases o3 with
              | none => simp at h3
              | some z =>
                simp only [Option.map_some, Option.some.injEq] at h3
                simp only []
                simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
                simp only [Slice.length, hr1, hr2] at hl hl2 hl3 h2 h3
                have : 6 ≤ val.val.length := by simp at hl3; omega
                simp [this, h1, h2, h3, List.drop_drop]
            · obtain ⟨rfl, -⟩ := ho3
              simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
              simp only [Slice.length, hr1, hr2] at hl hl2 hl3
              have : ¬ 6 ≤ val.val.length := by simp at hl3; omega
              simp [this]
        · obtain ⟨rfl, -⟩ := ho2
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          simp only [Slice.length, hr1] at hl hl2
          have : ¬ 6 ≤ val.val.length := by simp at hl2; omega
          simp [this]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      have : ¬ 6 ≤ val.val.length := by omega
      simp [this]
  case TimeZone =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u8_spec as ⟨o, r1, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, hr1⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only [lift, bind_ok]
        have hc : (UScalar.cast .Usize x).val = x.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
        step with slice_get_to as ⟨o1, h2⟩
        rw [hc] at h2
        obtain ⟨b, t, hbt⟩ : ∃ b t, val.val = b :: t := by
          cases hx : val.val with
          | nil => simp [Slice.length, hx] at hl
          | cons b t => exact ⟨b, t, rfl⟩
        rw [hbt] at h1 hr1
        simp [leNat] at h1 hr1
        split_ifs at h2 with hl2
        · obtain ⟨tx, rfl, htx⟩ := h2
          simp only []
          step with rawbytes_new_borrowed as ⟨rb, hrb⟩
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          rw [hbt]
          simp [lp1, takeExact, h1, hr1] at hl2 ⊢
          simp [hl2, hrb, htx, hr1]
          try omega
        · subst h2
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          rw [hbt]
          simp [lp1, takeExact, h1, hr1] at hl2 ⊢
          omega
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      have : val.val = [] := by cases hx : val.val <;> simp_all
      simp [this, lp1]
  case CatalogNz =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u8_spec as ⟨o, r1, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, hr1⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only [lift, bind_ok]
        have hc : (UScalar.cast .Usize x).val = x.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
        step with slice_get_to as ⟨o1, h2⟩
        rw [hc] at h2
        obtain ⟨b, t, hbt⟩ : ∃ b t, val.val = b :: t := by
          cases hx : val.val with
          | nil => simp [Slice.length, hx] at hl
          | cons b t => exact ⟨b, t, rfl⟩
        rw [hbt] at h1 hr1
        simp [leNat] at h1 hr1
        split_ifs at h2 with hl2
        · obtain ⟨tx, rfl, htx⟩ := h2
          simp only []
          step with rawbytes_new_borrowed as ⟨rb, hrb⟩
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          rw [hbt]
          simp [lp1, takeExact, h1, hr1] at hl2 ⊢
          simp [hl2, hrb, htx, hr1]
          try omega
        · subst h2
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          rw [hbt]
          simp [lp1, takeExact, h1, hr1] at hl2 ⊢
          omega
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      have : val.val = [] := by cases hx : val.val <;> simp_all
      simp [this, lp1]
  case LcTimeNames =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case CharsetDatabase =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case TableMapForUpdate =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u64_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case MasterDataWritten =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    sorry
  case Invoker =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    sorry
  case UpdatedDbNames =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    simp [statusVarKeyCode] at hk
  case Microseconds =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    simp [statusVarKeyCode] at hk
  case CommitTs =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    exact (WP.spec_ok _).mpr (by simp [svValRead, svValView, statusVarKeyCode])
  case CommitTs2 =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    exact (WP.spec_ok _).mpr (by simp [svValRead, svValView, statusVarKeyCode])
  case ExplicitDefaultsForTimestamp =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u8_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case DdlLoggedWithXid =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u64_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case DefaultCollationForUtf8mb4 =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case SqlRequirePrimaryKey =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u8_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case DefaultTableEncryption =>
    unfold binlog.events.query_event.StatusVar.get_value
    simp only []
    step with io.ParseBuf.checked_eat_u8_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some x =>
        simp only [Option.map_some, Option.some.injEq] at h1
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        subst_vars
        simp [hl, h1]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]

/-- **Upstream bug:** `get_value` of `Q_UPDATED_DB_NAMES` gives `dbNamesCrate` (the first name, then empty names), not the names of the format (`dbNames`); the raw value as the error without a count or a terminated first name. -/
theorem binlog.events.query_event.StatusVar.get_value_updated_db_names (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 12) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match v.value.val with
      | [] => r = .Err v.value
      | c :: rest => match dbNamesCrate c.val rest with
        | some ns => ∃ x, r = .Ok x ∧ svValView x = (12, [], ns)
        | none => r = .Err v.value ⦄ := by
  sorry

/-- `get_value` of `Q_MICROSECONDS` reads a 4-byte integer (the format has 3). -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => if 4 ≤ v.value.length then ∃ x, r = .Ok x ∧ svValView x = (13, [leNat (v.value.val.take 4)], [])
      else r = .Err v.value ⦄ := by
  obtain ⟨k, val⟩ := v
  cases k <;> simp only [statusVarKeyCode] at hk <;> try omega
  unfold binlog.events.query_event.StatusVar.get_value
  step with io.ParseBuf.checked_eat_u32_le_spec as ⟨o, rest, ho⟩
  split_ifs at ho ⊢ with hl
  · obtain ⟨h1, -⟩ := ho
    cases o with
    | none => simp at h1
    | some x =>
      simp only [Option.map_some, Option.some.injEq] at h1
      exact (WP.spec_ok _).mpr ⟨_, rfl, by simp [svValView, h1]⟩
  · obtain ⟨rfl, -⟩ := ho
    exact (WP.spec_ok _).mpr rfl

/-- **Upstream bug:** every `Q_MICROSECONDS` variable the iterator yields (3 bytes) fails to decode. -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds_bug (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 13) (hl : v.value.length = 3) :
    binlog.events.query_event.StatusVar.get_value v = ok (.Err v.value) := by
  have h := binlog.events.query_event.StatusVar.get_value_microseconds v hk
  have hl' : ¬ 4 ≤ v.value.length := by omega
  simp only [hl', ite_false] at h
  obtain ⟨r, hr, hp⟩ := PBUtil.spec_eq_ok h
  rw [hr, hp]

end mysql_common
