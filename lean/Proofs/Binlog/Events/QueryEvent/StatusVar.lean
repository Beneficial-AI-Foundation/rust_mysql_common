import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Io.ParseBuf
import Proofs.Util.RawBytesSeq

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
    step with io.ParseBuf.checked_eat_spec as ⟨o, r1, ho⟩
    split_ifs at ho with hl
    · obtain ⟨h1, -⟩ := ho
      cases o with
      | none => simp at h1
      | some bs =>
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only []
        have lb : bs.val.length = 4 := by rw [h1]; simp [Slice.length] at hl ⊢; omega
        step*
        simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
        simp only [Slice.length] at hl
        obtain ⟨a0, a1, a2, a3, h4⟩ : ∃ a0 a1 a2 a3, bs.val = [a0, a1, a2, a3] := by
          match hx : bs.val, lb with
          | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
        simp only [h4] at *
        simp [hl, ← h1, Array.make]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> subst_vars <;> rfl
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      simp [hl]
  case Invoker =>
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
        obtain ⟨b, t, hbt⟩ : ∃ b t, val.val = b :: t := by
          cases hx : val.val with
          | nil => simp [Slice.length, hx] at hl
          | cons b t => exact ⟨b, t, rfl⟩
        rw [hbt] at h1 hr1
        simp [leNat] at h1 hr1
        step with slice_get_to as ⟨o1, h2⟩
        rw [hc] at h2
        split_ifs at h2 with hl2
        · obtain ⟨un, rfl, hun⟩ := h2
          simp only []
          have hs : (UScalar.cast .Usize x).val ≤ r1.length := by rw [hc]; exact hl2
          simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, hs, ite_true,
            bind_ok]
          step with io.ParseBuf.checked_eat_u8_spec as ⟨o2, r2, ho2⟩
          simp only [Slice.drop, Slice.from_val, Slice.length, hc] at ho2
          split_ifs at ho2 with hl3
          · obtain ⟨h3, hr2⟩ := ho2
            cases o2 with
            | none => simp at h3
            | some y =>
              simp only [Option.map_some, Option.some.injEq] at h3
              simp only [lift, bind_ok]
              have hcy : (UScalar.cast .Usize y).val = y.val := IntAndMisc.cast_usize_small _ (by scalar_tac)
              obtain ⟨b2, t2, hbt2⟩ : ∃ b2 t2, r1.val.drop x.val = b2 :: t2 := by
                cases hx : r1.val.drop x.val with
                | nil => simp [hx] at hl3
                | cons b2 t2 => exact ⟨b2, t2, rfl⟩
              rw [hbt2] at h3 hr2
              simp [leNat] at h3 hr2
              step with slice_get_to as ⟨o3, h4⟩
              rw [hcy] at h4
              split_ifs at h4 with hl4
              · obtain ⟨hn, rfl, hhn⟩ := h4
                simp only []
                step with rawbytes_new_borrowed as ⟨rb, hrb⟩
                step with rawbytes_new_borrowed as ⟨rb2, hrb2⟩
                simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
                rw [hbt]
                rw [hr1] at hl2 hun hbt2
                rw [hr2] at hl4 hhn
                simp [lp1, takeExact, ← h1, hl2, hbt2, ← h3, hl4, hrb, hrb2, hun, hhn]
              · subst h4
                simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
                rw [hbt]
                rw [hr1] at hl2 hbt2
                rw [hr2] at hl4
                simp [lp1, takeExact, ← h1, hl2, hbt2, ← h3, hl4]
          · obtain ⟨rfl, -⟩ := ho2
            simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
            rw [hbt]
            rw [hr1] at hl2 hl3
            have : t.drop x.val = [] := List.drop_eq_nil_of_le (by simp at hl3; omega)
            simp [lp1, takeExact, ← h1, hl2, this]
        · subst h2
          simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
          rw [hbt]
          rw [hr1] at hl2
          simp [lp1, takeExact, ← h1, hl2]
    · obtain ⟨rfl, -⟩ := ho
      simp only [statusVarKeyCode, svValRead, ↓reduceIte, svValView]
      simp only [Slice.length] at hl
      have : val.val = [] := by cases hx : val.val <;> simp_all
      simp [this, lp1]
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

private theorem udn_loop_spec (read : Slice U8) :
    binlog.events.query_event.updated_db_names_loop read 0#usize ⦃ r => r.val ≤ read.length ∧
      (∀ b ∈ read.val.take r.val, b.val ≠ 0) ∧ (r.val < read.length → (read.val[r.val]!).val = 0) ⦄ := by
  unfold binlog.events.query_event.updated_db_names_loop
  apply loop.spec_decr_nat (fun i => read.length - i.val)
    (fun i => i.val ≤ read.length ∧ ∀ b ∈ read.val.take i.val, b.val ≠ 0)
  · rintro i ⟨hi, hall⟩
    unfold binlog.events.query_event.updated_db_names_loop.body
    step*
    · have hlt : i.val < read.length := by scalar_tac
      refine ⟨by omega, ?_, by omega⟩
      rw [index1_post, List.take_add_one, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
      intro b hb
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hall b hb
      · rw [← i1_post]; intro h0; apply (show ¬i1 = 0#u8 by simpa using ‹(i1 != 0#u8) = true›); simp [UScalar.eq_equiv, h0]
    · have hlt : i.val < read.length := by scalar_tac
      refine ⟨by omega, hall, fun _ => ?_⟩
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
      simp only [Option.getD_some, ← i1_post]
      have h0 : i1 = 0#u8 := UScalar.eq_of_val_eq (by simpa using ‹¬(i1 != 0#u8) = true›)
      rw [h0]; rfl
  · simp

private theorem hasNul_iff (l : List U8) : hasNul l = true ↔ ∃ b ∈ l, b.val = 0 := by
  simp [hasNul]

private theorem udn_spec : ∀ (n : Nat) (count : Usize) (read : Slice U8)
    (names : alloc.vec.Vec (misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit)),
    count.val = n → names.length + n < Usize.max →
    binlog.events.query_event.updated_db_names read count names ⦃ p =>
      if n = 0 then p.1 = some () ∧ p.2 = names
      else if hasNul read.val then p.1 = some () ∧ p.2.val.map (fun x => cowList x.1) =
        names.val.map (fun x => cowList x.1) ++ (beforeZero read.val :: List.replicate (n - 1) [])
      else p.1 = none ⦄ := by
  intro n
  induction n with
  | zero =>
    intro count read names hc _
    unfold binlog.events.query_event.updated_db_names
    have : count = 0#usize := UScalar.eq_of_val_eq (by simpa using hc)
    simp [this]
  | succ n ih =>
    intro count read names hc hb
    unfold binlog.events.query_event.updated_db_names
    have hne : count ≠ 0#usize := fun h => by subst h; simp at hc
    simp only [hne, ite_false]
    step with udn_loop_spec as ⟨idx, hidx1, hidx2, hidx3⟩
    simp only [Nat.add_one_ne_zero, ite_false]
    by_cases hz : idx.val = read.length
    · have hidx : idx = Slice.len read := UScalar.eq_of_val_eq (by simp [hz])
      simp only [hidx, ite_true]
      have hnn : hasNul read.val = false := by
        rw [Slice.length] at hz
        rw [hz, List.take_length] at hidx2
        cases hh : hasNul read.val
        · rfl
        · obtain ⟨b, hb, hb0⟩ := (hasNul_iff _).mp hh; exact absurd hb0 (hidx2 b hb)
      simp [hnn]
    · have hidx : idx ≠ Slice.len read := fun h => hz (by rw [h]; simp [Slice.length])
      simp only [hidx, ite_false]
      have hlt : idx.val < read.length := by omega
      have h0 := hidx3 hlt
      have hbz : beforeZero read.val = read.val.take idx.val :=
        PBUtil.beforeZero_of_zero _ _ (by simpa [Slice.length] using hlt) hidx2 h0
      have hnul : hasNul read.val = true := by
        rw [hasNul_iff]
        exact ⟨read.val[idx.val]!, by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
          simp, h0⟩
      simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index]
      have hs : idx.val ≤ read.length := hidx1
      simp only [hs, ite_true, bind_ok, hnul]
      step with rawbytes_new_borrowed as ⟨rb, hrb⟩
      step with alloc.vec.Vec.push_spec as ⟨names1, hn1⟩
      simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index, hs, ite_true, bind_ok]
      step as ⟨c1, hc1⟩
      have hd0 : (Slice.drop read idx).val = read.val.drop idx.val := by simp [Slice.drop]
      have hhead : ∃ t, (Slice.drop read idx).val = read.val[idx.val]! :: t := by
        rw [hd0, List.drop_eq_getElem_cons (by simpa [Slice.length] using hlt)]
        refine ⟨read.val.drop (idx.val + 1), ?_⟩
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
        rfl
      obtain ⟨t, ht⟩ := hhead
      have hnul' : hasNul (Slice.drop read idx).val = true := by
        rw [ht, hasNul_iff]; exact ⟨_, List.mem_cons_self, h0⟩
      have hbz' : beforeZero (Slice.drop read idx).val = [] := by
        have h0' : (read.val[idx.val]?.getD default).val = 0 := by rw [← List.getElem!_eq_getElem?_getD]; exact h0
        rw [ht, mysql_common.beforeZero_cons]; simp [h0']
      apply WP.spec_mono (ih c1 (Slice.drop read idx) names1 (by omega)
        (by simp [alloc.vec.Vec.length, hn1] at hb ⊢; omega))
      rintro ⟨o, ns⟩ hp
      simp only [hnul', ite_true, hbz'] at hp
      split_ifs at hp with hn0
      · obtain ⟨h1, h2⟩ := hp
        subst h2
        refine ⟨h1, ?_⟩
        simp [hn1, hrb, hbz, hn0]
      · obtain ⟨h1, h2⟩ := hp
        refine ⟨h1, ?_⟩
        rw [h2, hn1]
        simp [hrb, hbz]
        cases n with
        | zero => simp at hn0
        | succ m => simp [List.replicate_succ]

/-- **Upstream bug:** `get_value` of `Q_UPDATED_DB_NAMES` gives `dbNamesCrate` (the first name, then empty names), not the names of the format (`dbNames`); the raw value as the error without a count or a terminated first name. -/
theorem binlog.events.query_event.StatusVar.get_value_updated_db_names (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 12) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match v.value.val with
      | [] => r = .Err v.value
      | c :: rest => match dbNamesCrate c.val rest with
        | some ns => ∃ x, r = .Ok x ∧ svValView x = (12, [], ns)
        | none => r = .Err v.value ⦄ := by
  obtain ⟨k, val⟩ := v
  cases k <;> simp only [statusVarKeyCode] at hk <;> try omega
  unfold binlog.events.query_event.StatusVar.get_value
  simp only []
  step with io.ParseBuf.checked_eat_u8_spec as ⟨o, r1, ho⟩
  split_ifs at ho with hl
  · obtain ⟨h1, hr1⟩ := ho
    cases o with
    | none => simp at h1
    | some x =>
      simp only [Option.map_some, Option.some.injEq] at h1
      obtain ⟨b, t, hbt⟩ : ∃ b t, val.val = b :: t := by
        cases hx : val.val with
        | nil => simp [Slice.length, hx] at hl
        | cons b t => exact ⟨b, t, rfl⟩
      rw [hbt] at h1 hr1
      simp [leNat] at h1 hr1
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .Usize x).val = b.val := by
        rw [IntAndMisc.cast_usize_small _ (by scalar_tac), h1]
      step with udn_spec b.val (UScalar.cast .Usize x) r1 (alloc.vec.Vec.with_capacity _ _) hc
        (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length]; have := b.hBounds; scalar_tac) as ⟨o1, ns, hp⟩
      simp only [hbt, dbNamesCrate]
      rw [hr1] at hp
      by_cases h0 : b.val = 0
      · simp only [h0, ite_true] at hp ⊢
        obtain ⟨rfl, rfl⟩ := hp
        exact (WP.spec_ok _).mpr ⟨_, rfl, by simp [svValView, alloc.vec.Vec.with_capacity]⟩
      · simp only [h0, ite_false] at hp ⊢
        split_ifs at hp ⊢ with hn
        · obtain ⟨rfl, h2⟩ := hp
          exact (WP.spec_ok _).mpr ⟨_, rfl, by simp [svValView, h2, alloc.vec.Vec.with_capacity]⟩
        · rw [hp]; exact (WP.spec_ok _).mpr rfl
  · obtain ⟨rfl, -⟩ := ho
    have : val.val = [] := by simp [Slice.length] at hl; cases hx : val.val <;> simp_all
    simp [this]

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
