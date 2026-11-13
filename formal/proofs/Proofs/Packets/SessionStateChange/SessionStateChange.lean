import Defs
import Proofs.Util.StmtBulkSsB
import Proofs.Util.ParseBuf
import Proofs.Packets.SessionStateChange.SystemVariable
import Proofs.Misc.Raw.Array
import Proofs.Packets.SessionStateChange.Gtids
import Proofs.Packets.SessionStateChange.TransactionCharacteristics
import Proofs.Packets.SessionStateChange.TransactionState

/-! Statements for `enum SessionStateChange and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Helper lemmas: `Proofs/Util/StmtBulkSsB.lean` and below. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.SBSsB

private theorem checkedLenencInt_some_shrink (bs rest : List U8) (n : Nat)
    (h : checkedLenencInt bs = (some n, rest)) : rest.length < bs.length := by
  match bs with
  | [] => simp [checkedLenencInt] at h
  | b :: t =>
    simp only [checkedLenencInt] at h
    split_ifs at h with h1
    · simp at h; rw [← h.2]; simp
    · split at h
      · rename_i n' r' hd
        simp at h; rw [← h.2]
        simp only [lenencIntDecode] at hd
        split_ifs at hd
        · simp at hd; rw [← hd.2]; simp
        all_goals
          (try simp only [readLE] at hd)
          (try split_ifs at hd)
          all_goals (try simp at hd)
          all_goals (obtain ⟨_, _, rfl⟩ := hd; simp)
      · simp at h

private theorem checkedLenencStr_some_shrink (bs rest s : List U8)
    (h : checkedLenencStr bs = (some s, rest)) : rest.length < bs.length := by
  unfold checkedLenencStr at h
  split at h
  · simp at h
  · rename_i n r hr
    split_ifs at h with hle
    swap; · simp at h
    simp at h; rw [← h.2]
    have := checkedLenencInt_some_shrink _ _ _ hr
    simp; omega

private theorem sysVarRead_some_shrink (bs rest : List U8) (nv : List U8 × List U8)
    (h : sysVarRead bs = (some nv, rest)) : rest.length < bs.length := by
  unfold sysVarRead at h
  split at h
  · simp at h
  · rename_i n r1 h1
    split at h
    · simp at h
    · rename_i v r2 h2
      simp at h; rw [← h.2]
      have := checkedLenencStr_some_shrink _ _ _ h1
      have := checkedLenencStr_some_shrink _ _ _ h2
      omega

private theorem sysVarsFuel_fuel (n m : Nat) (bs : List U8) (hn : bs.length ≤ n) (hm : bs.length ≤ m) :
    sysVarsFuel n bs = sysVarsFuel m bs := by
  induction n generalizing m bs with
  | zero =>
    match bs with
    | [] => cases m <;> simp [sysVarsFuel]
    | _ :: _ => simp at hn
  | succ n ih =>
    match bs, m with
    | [], m => cases m <;> simp [sysVarsFuel]
    | _ :: _, 0 => simp at hm
    | b :: t, m + 1 =>
      simp only [sysVarsFuel]
      split
      · rfl
      · rename_i nv rest hr
        have := sysVarRead_some_shrink _ _ _ hr
        simp only [List.length_cons] at hn hm this
        rw [ih m rest (by omega) (by omega)]

private theorem sysVarsFuel_enc (vs : List (List U8 × List U8))
    (hvs : ∀ nv ∈ vs, nv.1.length < 2 ^ 64 ∧ nv.2.length < 2 ^ 64) (n : Nat)
    (hn : (vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)).length ≤ n) :
    sysVarsFuel n (vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)) = (some vs, []) := by
  induction vs generalizing n with
  | nil => cases n <;> simp [sysVarsFuel]
  | cons nv vs ih =>
    obtain ⟨h1, h2⟩ := hvs nv (by simp)
    have ne : lenencStr nv.1 ≠ [] := by unfold lenencStr lenencInt; split_ifs <;> simp
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil ne
    have hr : sysVarRead (lenencStr nv.1 ++ lenencStr nv.2 ++
        vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)) =
        (some nv, vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)) := by
      unfold sysVarRead
      simp only [List.append_assoc, checkedLenencStr_lenencStr _ _ h1, checkedLenencStr_lenencStr _ _ h2]
    cases n with
    | zero => simp [hx] at hn
    | succ n =>
      rw [List.flatMap_cons] at hn ⊢
      simp only [List.length_append] at hn
      have hne : lenencStr nv.1 ++ lenencStr nv.2 ++
          vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2) =
          x :: (xs ++ lenencStr nv.2 ++ vs.flatMap (fun nv => lenencStr nv.1 ++ lenencStr nv.2)) := by
        simp [hx]
      rw [hne, sysVarsFuel, ← hne, hr]
      simp only
      · rw [ih (fun nv h => hvs nv (by simp [h])) n (by simp [hx] at hn ⊢; omega)]
      · simp

end mysql_common.SBSsB

namespace mysql_common.SBSsB

private abbrev svPair (v : packets.session_state_change.SystemVariable) : List U8 × List U8 :=
  (cowList v.«name».1, cowList v.value.1)

private theorem rawbytes_new_vec_spec (v : alloc.vec.Vec U8) :
    misc.raw.bytes.RawBytes.new misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple
      (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec core.clone.CloneU8)) v
      ⦃ r => cowList r.1 = v.val ⦄ := by
  rw [misc.raw.bytes.RawBytes.new_eq _ _ v (.Owned v) rfl]
  exact (WP.spec_ok _).mpr rfl

private theorem to_owned_static_spec (sv : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.to_owned_static sv ⦃ x => svPair x = svPair sv ⦄ := by
  unfold packets.session_state_change.SystemVariable.to_owned_static
  step with PCSUtil.lenenc_as_bytes as ⟨ s, hs ⟩
  step with alloc.slice.Slice.to_vec_spec as ⟨ v, hv ⟩
  step with rawbytes_new_vec_spec as ⟨ rb, hrb ⟩
  step with PCSUtil.lenenc_as_bytes as ⟨ s1, hs1 ⟩
  step with alloc.slice.Slice.to_vec_spec as ⟨ v1, hv1 ⟩
  step with rawbytes_new_vec_spec as ⟨ rb1, hrb1 ⟩
  simp only [hrb, hrb1, ← hs, ← hs1, hv, hv1]
  exact ⟨rfl, rfl⟩

private theorem to_owned_loop_spec (x : Slice packets.session_state_change.SystemVariable) (k : Nat) (i : Usize)
    (vars : alloc.vec.Vec packets.session_state_change.SystemVariable)
    (hk : x.length - i.val = k) (hi : i.val ≤ x.length) (hcap : vars.length + k ≤ Usize.max) :
    packets.session_state_change.system_variables_to_owned x i vars ⦃ r =>
      r.val.map svPair = vars.val.map svPair ++ (x.val.drop i.val).map svPair ⦄ := by
  induction k generalizing i vars with
  | zero =>
    rw [packets.session_state_change.system_variables_to_owned]
    have : ¬ i < x.len := by scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok]
    rw [List.drop_of_length_le (by simp at hk ⊢; omega)]; simp
  | succ k ih =>
    rw [packets.session_state_change.system_variables_to_owned]
    have hlt : i < x.len := by scalar_tac
    have hlt' : i.val < x.val.length := by scalar_tac
    simp only [hlt, ↓reduceIte]
    step with Slice.index_usize_spec as ⟨sv, hsv⟩
    step with to_owned_static_spec as ⟨sv1, hsv1, hsv1'⟩
    step with alloc.vec.Vec.push_spec as ⟨vars1, hvars1⟩
    step as ⟨i2, hi2⟩
    apply WP.spec_mono (ih i2 vars1 (by scalar_tac) (by scalar_tac) (by simp [hvars1]; scalar_tac))
    intro r hr
    rw [hr, hvars1, List.drop_eq_getElem_cons hlt']
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append, hi2]
    simp [svPair, hsv1, hsv1', hsv]

private theorem serialize_loop_spec (x : Slice packets.session_state_change.SystemVariable) (k : Nat) (i : Usize)
    (buf : alloc.vec.Vec U8)
    (hk : x.length - i.val = k) (hi : i.val ≤ x.length)
    (hcap : buf.length + ((x.val.drop i.val).flatMap (fun v => lenencStr (cowList v.«name».1) ++ lenencStr (cowList v.value.1))).length ≤ Usize.max) :
    packets.session_state_change.serialize_system_variables x i buf ⦃ r =>
      r.val = buf.val ++ (x.val.drop i.val).flatMap (fun v => lenencStr (cowList v.«name».1) ++ lenencStr (cowList v.value.1)) ⦄ := by
  induction k generalizing i buf with
  | zero =>
    rw [packets.session_state_change.serialize_system_variables]
    have : ¬ i < x.len := by scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok]
    rw [List.drop_of_length_le (by simp at hk ⊢; omega)]; simp
  | succ k ih =>
    rw [packets.session_state_change.serialize_system_variables]
    have hlt : i < x.len := by scalar_tac
    have hlt' : i.val < x.val.length := by scalar_tac
    simp only [hlt, ↓reduceIte]
    rw [List.drop_eq_getElem_cons hlt'] at hcap
    simp only [List.flatMap_cons, List.length_append] at hcap
    step with Slice.index_usize_spec as ⟨sv, hsv⟩
    step with packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, hbuf1⟩
    step as ⟨i2, hi2⟩
    apply WP.spec_mono (ih i2 buf1 (by scalar_tac) (by scalar_tac) ?_)
    · intro r hr
      rw [hr, hbuf1, List.drop_eq_getElem_cons hlt', hsv, hi2]
      simp only [List.flatMap_cons, List.append_assoc]
    · show buf1.val.length + _ ≤ _
      rw [hbuf1, hi2]; subst hsv
      simp only [List.length_append]
      have : buf.length = buf.val.length := rfl
      omega

private theorem sysVarsFuel_cons_step (b : U8) (t : List U8) :
    sysVarsFuel (b :: t).length (b :: t) =
      match sysVarRead (b :: t) with
      | (none, rest) => (none, rest)
      | (some nv, rest) =>
        match sysVarsFuel rest.length rest with
        | (some vs, r) => (some (nv :: vs), r)
        | (none, r) => (none, r) := by
  rw [List.length_cons, sysVarsFuel]
  · split
    · rename_i h; rw [h]
    · rename_i nv rest hr
      have := sysVarRead_some_shrink _ _ _ hr
      simp only [List.length_cons] at this
      rw [hr]; simp only
      rw [sysVarsFuel_fuel t.length rest.length rest (by omega) (by omega)]
      cases sysVarsFuel rest.length rest with
      | mk o r => cases o <;> rfl
  · simp

private theorem deser_loop_spec (h64 : Target64) (n : Nat) (buf : io.ParseBuf)
    (vars : alloc.vec.Vec packets.session_state_change.SystemVariable)
    (hn : buf.val.length ≤ n) (hcap : vars.length + buf.val.length ≤ Usize.max) :
    packets.session_state_change.deserialize_system_variables buf vars ⦃ r rest =>
      ((okPart r).map (fun v => v.val.map svPair), rest.val) =
        ((sysVarsFuel buf.val.length buf.val).1.map (vars.val.map svPair ++ ·),
          (sysVarsFuel buf.val.length buf.val).2) ⦄ := by
  induction n generalizing buf vars with
  | zero =>
    have he : buf.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [packets.session_state_change.deserialize_system_variables]
    step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
    have : b = true := by simpa [he] using hb
    simp [this, he, sysVarsFuel, okPart]
  | succ n ih =>
    rw [packets.session_state_change.deserialize_system_variables]
    step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
    split
    · rename_i hbt
      have he : buf.val = [] := hb.mp hbt
      simp [he, sysVarsFuel, okPart]
    · rename_i hbt
      have hne : buf.val ≠ [] := fun h => hbt (hb.mpr h)
      obtain ⟨b0, t, hbt'⟩ := List.exists_cons_of_ne_nil hne
      have hd : io.ParseBuf.parse_unchecked
          packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple buf ()
          ⦃ r rest => ((okPart r).map svPair, rest.val) = sysVarRead buf.val ⦄ := by
        rw [io.ParseBuf.parse_unchecked_eq]
        exact packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf
      step with hd as ⟨r, buf1, hr⟩
      rw [hbt', sysVarsFuel_cons_step, ← hbt']
      cases r with
      | Err e =>
        simp only [okPart, Option.map_none] at hr
        rw [← hr]
        simp [okPart]
      | Ok sv =>
        simp only [okPart, Option.map_some] at hr
        have hshr := sysVarRead_some_shrink _ _ _ hr.symm
        rw [← hr]
        simp only
        step with alloc.vec.Vec.push_spec as ⟨vars1, hvars1⟩
        have e1 : vars1.val.length = vars.val.length + 1 := by simp [hvars1]
        have e2 : vars.length = vars.val.length := rfl
        apply WP.spec_mono (ih buf1 vars1 (by omega) (by
          show vars1.val.length + _ ≤ _
          omega))
        rintro ⟨r2, rest2⟩ h2
        simp only [WP.uncurry', Prod.mk.injEq] at h2 ⊢
        rw [h2.1, h2.2, hvars1]
        cases sysVarsFuel buf1.val.length buf1.val with
        | mk o rr => cases o <;> simp [svPair]

end mysql_common.SBSsB

namespace mysql_common

private theorem index_49_spec :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice U8))
      (Array.make 1#usize [49#u8]) () ⦃ s => s.val = [49#u8] ⦄ := by
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index, Array.to_slice]

private theorem schema_deser_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄ := by
  unfold packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact SBSsB.lenenc_parse_rewrap h64 buf

private theorem slice_u8_eq_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ (b : Bool) => b ↔ (s1.val = s2.val) ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ ?_)
  · intro b hb; rw [hb, Slice.eq_iff]
  · intro x y; simp


/-- `into_owned`: the same change. -/
theorem packets.session_state_change.SessionStateChange.into_owned_spec (self : packets.session_state_change.SessionStateChange) :
    packets.session_state_change.SessionStateChange.into_owned self ⦃ c => SsChange.of c = SsChange.of self ⦄ := by
  cases self with
  | IsTracked b => simp [packets.session_state_change.SessionStateChange.into_owned]
  | Schema s =>
    unfold packets.session_state_change.SessionStateChange.into_owned packets.session_state_change.Schema.into_owned
    apply WP.spec_bind (WP.spec_bind (PCSUtil.raw_into_owned _ s) (fun x hx => (WP.spec_ok x).mpr hx))
    intro x hx; simp [SsChange.of, hx]
  | SystemVariables x =>
    unfold packets.session_state_change.SessionStateChange.into_owned
    simp only
    apply WP.spec_bind (SBSsB.to_owned_loop_spec _ _ 0#usize _ rfl (by simp)
      (by simp [alloc.vec.Vec.with_capacity]))
    intro v hv
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.deref] at hv
    simp [SsChange.of, hv]
  | Gtids g =>
    unfold packets.session_state_change.SessionStateChange.into_owned packets.session_state_change.Gtids.into_owned
    apply WP.spec_bind (WP.spec_bind (PCSUtil.raw_into_owned _ g) (fun x hx => (WP.spec_ok x).mpr hx))
    intro x hx; simp [SsChange.of, hx]
  | TransactionCharacteristics t =>
    unfold packets.session_state_change.SessionStateChange.into_owned
    apply WP.spec_bind (packets.session_state_change.TransactionCharacteristics.into_owned_spec t)
    intro x hx; simp [SsChange.of, hx]
  | TransactionState t =>
    unfold packets.session_state_change.SessionStateChange.into_owned
    apply WP.spec_bind (packets.session_state_change.TransactionState.into_owned_spec t)
    intro x hx; simp [SsChange.of, hx]
  | Unsupported u =>
    unfold packets.session_state_change.SessionStateChange.into_owned packets.session_state_change.Unsupported.into_owned
    apply WP.spec_bind (WP.spec_bind (PCSUtil.raw_into_owned _ u) (fun x hx => (WP.spec_ok x).mpr hx))
    intro x hx; simp [SsChange.of, hx]

/-- `MyDeserialize for SessionStateChange`: `SIZE` is `None`. -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE_eq :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE = none := by
  unfold packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE; rfl

/-- `MyDeserialize for SessionStateChange` with the type `ty`: total; `ssChangeRead ty` (the
    protocol's `data` layout of that type; system variables until the input is exhausted;
    `IsTracked` is `true` exactly for `"1"`). -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec
    (h64 : Target64) (ty : constants.SessionStateType) (buf : io.ParseBuf) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      ((okPart r).map SsChange.of, rest.val) = ssChangeRead ty buf.val ⦄ := by
  unfold packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize
  cases ty with
  | SESSION_TRACK_SYSTEM_VARIABLES =>
    simp only
    apply WP.spec_bind (SBSsB.deser_loop_spec h64 _ buf _ le_rfl (by simp [alloc.vec.Vec.new]))
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry', Prod.mk.injEq] at h
    simp only [ssChangeRead]
    obtain ⟨h1, h2⟩ := h
    revert h1 h2
    generalize sysVarsFuel buf.val.length buf.val = p
    rcases p with ⟨o, rr⟩
    intro h1 h2
    cases o <;> cases r <;> simp_all [okPart, SsChange.of, alloc.vec.Vec.new]
  | SESSION_TRACK_SCHEMA =>
    rw [io.ParseBuf.parse_unchecked_eq]
    apply WP.spec_bind (schema_deser_spec h64 buf)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'] at h
    simp only [ssChangeRead, lenencAs]
    revert h
    generalize checkedLenencStr buf.val = p
    rcases p with ⟨o, rr⟩
    intro h
    cases o <;> cases r <;> simp_all [okPart, SsChange.of]
  | SESSION_TRACK_STATE_CHANGE =>
    rw [io.ParseBuf.parse_unchecked_eq]
    apply WP.spec_bind (PCSUtil.lenenc_raw_deserialize' h64 buf)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'] at h
    simp only [ssChangeRead, lenencAs]
    cases r with
    | Err e =>
      rw [h]
      simp [okPart, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok rb =>
      simp only [okPart, core.result.Result.Insts.CoreOpsTry.branch]
      step with PCSUtil.lenenc_as_bytes as ⟨s, hs⟩
      step with index_49_spec as ⟨s1, hs1⟩
      step with slice_u8_eq_spec as ⟨b, hb⟩
      rw [h]
      have h49 : (byte 49 : U8) = 49#u8 := by rfl
      simp only [okPart, Option.map_some, SsChange.of, h49, Prod.mk.injEq, and_true, Option.some.injEq,
        SsChange.isTracked.injEq]
      rw [← hs, ← hs1]
      cases b <;> simp_all
  | SESSION_TRACK_GTIDS =>
    rw [io.ParseBuf.parse_unchecked_eq]
    apply WP.spec_bind (packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'] at h
    simp only [ssChangeRead]
    revert h
    generalize gtidsRead buf.val = p
    rcases p with ⟨o, rr⟩
    intro h
    cases o <;> cases r <;> simp_all [okPart, SsChange.of, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | SESSION_TRACK_TRANSACTION_CHARACTERISTICS =>
    rw [io.ParseBuf.parse_unchecked_eq]
    apply WP.spec_bind (packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'] at h
    simp only [ssChangeRead, lenencAs]
    revert h
    generalize checkedLenencStr buf.val = p
    rcases p with ⟨o, rr⟩
    intro h
    cases o <;> cases r <;> simp_all [okPart, SsChange.of, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | SESSION_TRACK_TRANSACTION_STATE =>
    rw [io.ParseBuf.parse_unchecked_eq]
    apply WP.spec_bind (packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'] at h
    simp only [ssChangeRead, lenencAs]
    revert h
    generalize checkedLenencStr buf.val = p
    rcases p with ⟨o, rr⟩
    intro h
    cases o <;> cases r <;> simp_all [okPart, SsChange.of]

/-- Round trip: the `data` of a change (`ssChangeEnc`), read with the change's type, gives the
    change back (for system variables the data must end there, as the reader takes pairs until
    the input is exhausted). `Unsupported` has no type and is never read. -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.roundtrip
    (h64 : Target64) (c : packets.session_state_change.SessionStateChange) (ty : constants.SessionStateType)
    (hty : (SsChange.of c).type? = some ty)
    (tail : List U8) (htail : tail = [] ∨ ty ≠ .SESSION_TRACK_SYSTEM_VARIABLES) (buf : io.ParseBuf)
    (h : buf.val = ssChangeEnc (SsChange.of c) ++ tail) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      (okPart r).map SsChange.of = some (SsChange.of c) ∧ rest.val = tail ⦄ := by
  have hl : ∀ x : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit, (cowList x.1).length < 2 ^ 64 :=
    fun x => lt_two_pow_64_of_le_max (PCSUtil.cowList_length_le _)
  have hread : ssChangeRead ty buf.val = (some (SsChange.of c), tail) := by
    rw [h]
    cases c with
    | IsTracked b =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      cases b
      · simp [SsChange.of, ssChangeRead, ssChangeEnc, lenencAs, checkedLenencStr_lenencStr]; decide
      · simp [SsChange.of, ssChangeRead, ssChangeEnc, lenencAs, checkedLenencStr_lenencStr]
    | Schema x =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      simp [SsChange.of, ssChangeRead, ssChangeEnc, lenencAs, checkedLenencStr_lenencStr _ _ (hl x)]
    | SystemVariables vars =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      have ht : tail = [] := by simpa using htail
      subst ht
      simp only [SsChange.of, ssChangeRead, ssChangeEnc, List.append_nil]
      rw [SBSsB.sysVarsFuel_enc _ (by intro nv hnv; simp at hnv; obtain ⟨a, _, rfl⟩ := hnv; exact ⟨hl _, hl _⟩) _ le_rfl]
    | Gtids g =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      simp [SsChange.of, ssChangeRead, ssChangeEnc, gtidsRead, checkedLenencStr_lenencStr _ _ (hl g)]
    | TransactionCharacteristics x =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      simp [SsChange.of, ssChangeRead, ssChangeEnc, lenencAs, checkedLenencStr_lenencStr _ _ (hl x)]
    | TransactionState x =>
      simp only [SsChange.of, SsChange.type?, Option.some.injEq] at hty; subst hty
      simp [SsChange.of, ssChangeRead, ssChangeEnc, lenencAs, checkedLenencStr_lenencStr _ _ (hl x)]
    | Unsupported u => simp [SsChange.of, SsChange.type?] at hty
  apply WP.spec_mono (packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec h64 ty buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry', hread, Prod.mk.injEq] at hr ⊢
  exact hr

/-- `MySerialize for SessionStateChange`: appends `ssChangeEnc` (the protocol's `data`; for
    `IsTracked`, `"1"` or `"0"`). -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SessionStateChange) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssChangeEnc (SsChange.of self)).length ≤ Usize.max) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssChangeEnc (SsChange.of self) ⦄ := by
  unfold packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize
  cases self with
  | IsTracked b =>
    cases b
    · apply WP.spec_mono (ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec _ buf (by
        simp [SsChange.of, ssChangeEnc, lenencStr, lenencInt] at h; simpa using h))
      intro r hr; rw [hr]; simp [SsChange.of, ssChangeEnc, lenencStr, lenencInt, Array.make]; exact ⟨rfl, rfl⟩
    · apply WP.spec_mono (ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec _ buf (by
        simp [SsChange.of, ssChangeEnc, lenencStr, lenencInt] at h; simpa using h))
      intro r hr; rw [hr]; simp [SsChange.of, ssChangeEnc, lenencStr, lenencInt, Array.make]; exact ⟨rfl, rfl⟩
  | Schema x =>
    unfold packets.session_state_change.Schema.Insts.Mysql_commonProtoMySerialize.serialize
    exact PCSUtil.lenenc_raw_serialize x buf h
  | SystemVariables vars =>
    simp only
    apply WP.spec_mono (SBSsB.serialize_loop_spec _ _ 0#usize buf rfl (by simp) (by
      simpa [SsChange.of, ssChangeEnc, alloc.vec.Vec.deref, List.flatMap_map] using h))
    intro r hr
    rw [hr]
    simp [SsChange.of, ssChangeEnc, alloc.vec.Vec.deref, List.flatMap_map]
  | Gtids g =>
    exact packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize_spec g buf h
  | TransactionCharacteristics t =>
    exact packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize_spec t buf h
  | TransactionState t =>
    exact packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMySerialize.serialize_spec t buf h
  | Unsupported u =>
    unfold packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize
    exact PCSUtil.lenenc_raw_serialize u buf h

end mysql_common
