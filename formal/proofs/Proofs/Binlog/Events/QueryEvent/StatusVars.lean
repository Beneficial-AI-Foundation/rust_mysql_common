import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Binlog.Events.QueryEvent.StatusVarsIterator

/-! Statements for `struct StatusVars and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `iter`: an iterator at position 0 over the block (its first 65535 bytes). -/
theorem binlog.events.query_event.StatusVars.iter_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.iter s ⦃ it => it.pos.val = 0 ∧ it.status_vars.val = (cowList s.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.StatusVars.iter binlog.events.query_event.StatusVarsIterator.new
  apply WP.spec_bind (misc.raw.bytes.RawBytes.as_bytes_spec _ 65535#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) s)
  intro sl hsl
  exact (WP.spec_ok _).mpr ⟨rfl, hsl⟩

namespace SVFind

private theorem ofCode_code (a : binlog.consts.StatusVarKey) : statusVarKeyOfCode (statusVarKeyCode a) = some a := by
  cases a <;> rfl

private theorem code_inj (a b : binlog.consts.StatusVarKey) (h : statusVarKeyCode a = statusVarKeyCode b) : a = b := by
  have h1 := ofCode_code a
  rw [h, ofCode_code b] at h1
  exact (Option.some.inj h1).symm

private theorem disc_val (a : binlog.consts.StatusVarKey) : (read_discriminant a).val = statusVarKeyCode a := by
  cases a <;> rfl

private theorem key_eq (a b : binlog.consts.StatusVarKey) :
    binlog.consts.StatusVarKey.Insts.CoreCmpPartialEqStatusVarKey.eq a b =
      ok (decide (statusVarKeyCode a = statusVarKeyCode b)) := by
  simp only [binlog.consts.StatusVarKey.Insts.CoreCmpPartialEqStatusVarKey.eq, ← disc_val]
  congr 2
  apply propext; constructor
  · intro h; simp only [read_discriminant] at *; rw [h]
  · intro h; exact UScalar.eq_of_val_eq h

/-- The walk does not depend on the fuel once there is enough. -/
private theorem svWalk_fuel : ∀ (f g : Nat) (l : List U8), l.length < f → l.length < g → svWalk f l = svWalk g l := by
  intro f
  induction f with
  | zero => intro g l h; omega
  | succ f ih =>
    intro g l hf hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    cases l with
    | nil => simp [svWalk]
    | cons k rest =>
      simp only [svWalk]
      split
      · rfl
      · cases svValueLen k.val rest with
        | none => rfl
        | some n =>
          by_cases hn : n ≤ rest.length
          · simp only [hn, ↓reduceIte, List.cons.injEq, true_and]
            simp only [List.length_cons] at hf hg
            exact ih g _ (by simp; omega) (by simp; omega)
          · simp [hn]

private theorem walk_step (bs : List U8) (pos : Nat) (kv : Nat × List U8) (p : Nat)
    (h : svStep bs pos = some (kv, p)) :
    statusVarsOf (bs.drop pos) = kv :: statusVarsOf (bs.drop p) := by
  rw [SVIter.svStep_eq] at h
  unfold statusVarsOf
  cases hd : bs.drop pos with
  | nil => rw [hd] at h; simp at h
  | cons k rest =>
    rw [hd] at h
    simp only at h
    by_cases hk : statusVarKeyOfCode k.val = none
    · simp [hk] at h
    · simp only [hk, ite_false] at h
      cases hv : svValueLen k.val rest with
      | none => rw [hv] at h; simp at h
      | some n =>
        rw [hv] at h
        by_cases hn : n ≤ rest.length
        · simp only [hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hp : bs.drop (pos + 1 + n) = rest.drop n := by
            rw [show pos + 1 + n = pos + (n + 1) by omega, ← List.drop_drop, hd, List.drop_succ_cons]
          simp only [List.length_cons, svWalk, hk, hv, hn, ↓reduceIte, List.cons.injEq, true_and, hp]
          exact svWalk_fuel _ _ _ (by simp only [List.length_drop]; omega) (by omega)
        · simp [hn] at h

private theorem walk_none (bs : List U8) (pos : Nat) (h : svStep bs pos = none) :
    statusVarsOf (bs.drop pos) = [] := by
  unfold svStep at h
  split at h
  · simp at h
  · rename_i hh
    cases hw : statusVarsOf (bs.drop pos) with
    | nil => rfl
    | cons a t => rw [hw] at hh; simp at hh

theorem find_spec (needle : binlog.consts.StatusVarKey) : ∀ (m : Nat) (it : binlog.events.query_event.StatusVarsIterator),
    it.status_vars.length - it.pos.val = m → it.status_vars.length + 2 ^ 16 ≤ Usize.max →
    binlog.events.query_event.find_status_var it needle ⦃ r =>
      r.1.map (fun x => (statusVarKeyCode x.key, x.value.val)) =
        (statusVarsOf (it.status_vars.val.drop it.pos.val)).find? (fun kv => kv.1 = statusVarKeyCode needle) ⦄ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro it hm hlen
    unfold binlog.events.query_event.find_status_var
    apply WP.spec_bind (binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next_spec it hlen)
    rintro ⟨o, it'⟩ h
    simp only [WP.uncurry'] at h
    cases hs : svStep it.status_vars.val it.pos.val with
    | none =>
      rw [hs] at h
      obtain ⟨rfl, -⟩ := h
      simp [walk_none _ _ hs]
    | some r =>
      obtain ⟨kv, p⟩ := r
      rw [hs] at h
      obtain ⟨ho, hp, hsv⟩ := h
      rw [walk_step _ _ _ _ hs]
      cases o with
      | none => simp at ho
      | some sv =>
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        simp only [key_eq, bind_ok]
        by_cases hk : statusVarKeyCode sv.key = statusVarKeyCode needle
        · change (if decide (statusVarKeyCode sv.key = statusVarKeyCode needle) = true then ok (some sv, it')
            else binlog.events.query_event.find_status_var it' needle) ⦃ r =>
            Option.map (fun x => (statusVarKeyCode x.key, x.value.val)) r.1 =
              List.find? (fun kv => decide (kv.1 = statusVarKeyCode needle))
                ((statusVarKeyCode sv.key, sv.value.val) :: statusVarsOf (List.drop p it.status_vars.val)) ⦄
          simp [hk]
        · change (if decide (statusVarKeyCode sv.key = statusVarKeyCode needle) = true then ok (some sv, it')
            else binlog.events.query_event.find_status_var it' needle) ⦃ r =>
            Option.map (fun x => (statusVarKeyCode x.key, x.value.val)) r.1 =
              List.find? (fun kv => decide (kv.1 = statusVarKeyCode needle))
                ((statusVarKeyCode sv.key, sv.value.val) :: statusVarsOf (List.drop p it.status_vars.val)) ⦄
          simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hlt : p > it.pos.val ∧ it.pos.val < it.status_vars.length := by
            rw [SVIter.svStep_eq] at hs
            have hslen : it.status_vars.length = it.status_vars.val.length := rfl
            cases hd : it.status_vars.val.drop it.pos.val with
            | nil => rw [hd] at hs; simp at hs
            | cons k rest =>
              have : it.pos.val < it.status_vars.val.length := by
                by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hd; simp at hd
              rw [hd] at hs
              simp only at hs
              split at hs
              · simp at hs
              · split at hs
                · simp at hs
                · split at hs
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; omega
                  · simp at hs
          have hsl : it'.status_vars.length = it.status_vars.length := by rw [hsv]
          apply WP.spec_mono (ih (it'.status_vars.length - it'.pos.val) (by omega) it' rfl (by omega))
          intro r hr
          rw [hr, hsv, hp]
          simp [hk]

end SVFind

/-- `get_status_var(key)`: the first variable with that key in the walk, if any. -/
theorem binlog.events.query_event.StatusVars.get_status_var_spec (s : binlog.events.query_event.StatusVars) (k : binlog.consts.StatusVarKey) :
    binlog.events.query_event.StatusVars.get_status_var s k ⦃ o => o.map (fun x => (statusVarKeyCode x.key, x.value.val)) =
      (statusVarsOf ((cowList s.1).take 65535)).find? (fun kv => kv.1 = statusVarKeyCode k) ⦄ := by
  unfold binlog.events.query_event.StatusVars.get_status_var
  apply WP.spec_bind (binlog.events.query_event.StatusVars.iter_spec s)
  intro it ⟨hp, hv⟩
  have hl : it.status_vars.length ≤ 65535 := by
    have : it.status_vars.length = it.status_vars.val.length := rfl
    rw [this, hv]; simp
  apply WP.spec_bind (SVFind.find_spec k _ it rfl (by scalar_tac))
  rintro ⟨o, _⟩ h
  simp only [hp, hv, List.drop_zero] at h
  exact (WP.spec_ok _).mpr h

/-- `into_owned`: the same bytes. -/
theorem binlog.events.query_event.StatusVars.into_owned_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.into_owned s ⦃ s' => cowList s'.1 = cowList s.1 ⦄ := by
  unfold binlog.events.query_event.StatusVars.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  exact hrb

/-- `MyDeserialize` with the length `len`: total; that many bytes, an error with the buffer unchanged if fewer. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec (len : U16) (buf : io.ParseBuf) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize
  have hc : (UScalar.cast .Usize len).val = len.val := IntAndMisc.cast_usize_small len (by scalar_tac)
  simp only [lift, bind_ok]
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq, misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq])]
  have h := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65535#usize) (UScalar.cast .Usize len) buf
    (fun o rest => if (UScalar.cast .Usize len).val ≤ buf.length then
        o = some (buf.val.take (UScalar.cast .Usize len).val) ∧ rest.val = buf.val.drop (UScalar.cast .Usize len).val
      else o = none ∧ rest = buf)
    (by
      apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec 65535#usize (UScalar.cast .Usize len) buf)
      rintro ⟨r, rest⟩ hr
      split_ifs at hr ⊢
      · exact hr
      · exact ⟨by simp [hr.1], hr.2⟩)
  step with h as ⟨r, rest, hr⟩
  rw [hc] at hr
  cases r with
  | Ok rb =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply (WP.spec_ok _).mpr
    split_ifs at hr ⊢ <;> simp_all
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    split_ifs at hr ⊢ <;> simp_all

/-- `MySerialize`: the bytes, truncated to 65535. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec (s : binlog.events.query_event.StatusVars) (buf : alloc.vec.Vec U8) (h : buf.length + min (cowList s.1).length 65535 ≤ Usize.max) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize s buf ⦃ buf' => buf'.val = buf.val ++ (cowList s.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro sl hsl
  apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec 65535#usize sl buf (by simp only [Slice.length, hsl]; exact h))
  intro b hb; simp [hb, hsl]

end mysql_common
