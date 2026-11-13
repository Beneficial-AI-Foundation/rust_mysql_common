import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Seq.Seq
import Proofs.Misc.Raw.Seq.Unknown
import Proofs.Packets.StmtBulkExecuteParamType
import Proofs.Packets.StmtBulkExecuteParamValues
import Proofs.Util.SharedBasic

/-! Statements for `struct ComStmtBulkExecuteRequest and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.Shared

namespace mysql_common

/-- `stmt_id`: the statement id. -/
theorem packets.ComStmtBulkExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.stmt_id self = ok self.stmt_id.1 := by
  rfl

/-- `bulk_flags`: the flags. -/
theorem packets.ComStmtBulkExecuteRequest.impl.bulk_flags_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.bulk_flags self = ok self.bulk_flags.1 := by
  rfl

/-- `types`: the parameter types. -/
theorem packets.ComStmtBulkExecuteRequest.impl.types_spec (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.types self ⦃ s => s.val = cowList self.types.1 ⦄ := by
  exact misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec _ _

/-- `values`: the values. -/
theorem packets.ComStmtBulkExecuteRequest.impl.values_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.values self = ok self.values := by
  rfl

/-- `MyDeserialize for ComStmtBulkExecuteRequest`: `SIZE` is `None`. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none := by
  unfold packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE; rfl

/-! ## Reading the parameter types -/

private theorem bulkTypesRead_succ (n : Nat) (bs : List U8) :
    bulkTypesRead (n + 1) bs = match (bulkTypeRead (bs.take 3)).1 with
      | none => none
      | some t => (bulkTypesRead n (bs.drop 3)).map (t :: ·) := by
  rw [bulkTypesRead]
  rcases (bulkTypeRead (bs.take 3)).1 with _ | t <;> rcases bulkTypesRead n (bs.drop 3) with _ | ts <;> rfl

private theorem types_loop (n : Nat) (it : core.ops.range.Range Usize) (buf : io.ParseBuf)
    (seq : alloc.vec.Vec packets.StmtBulkExecuteParamType)
    (hlen : it.end.val = it.start.val + n) (hcap : seq.length + n ≤ Usize.max)
    (hb : buf.val.length = 3 * n) :
    misc.raw.seq.parse_items_loop packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple
      it buf seq ⦃ r _ =>
      (okPart r).map (fun c => (cowList c).map SBParam.ptOf) =
        (bulkTypesRead n buf.val).map (fun ts => seq.val.map SBParam.ptOf ++ ts) ⦄ := by
  induction n generalizing it buf seq with
  | zero =>
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show ¬ (it.start.val < it.end.val) by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp_all [okPart, cowList, bulkTypesRead]
  | succ n ih =>
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show it.start.val < it.end.val by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    have hp := packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec buf
    obtain ⟨⟨r, buf1⟩, hrv, hr⟩ := PBUtil.spec_eq_ok hp
    rw [hrv]; simp only [bind_ok]
    have h3 : 3 ≤ Slice.length buf := by simp only [Slice.length]; omega
    simp only [h3, ite_true] at hr
    obtain ⟨hr1, hr2⟩ := hr
    rw [bulkTypesRead_succ]
    cases r with
    | Err e =>
      simp only [okPart, Option.map_none] at hr1
      rw [← hr1]
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart]
    | Ok v =>
      simp only [okPart, Option.map_some] at hr1
      rw [← hr1]
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with alloc.vec.Vec.push_spec seq v (by simp at hcap; scalar_tac) as ⟨ seq1, hseq1 ⟩
      have := ih it1 buf1 seq1 (by rw [he, ho2]; omega) (by simp [hseq1] at *; scalar_tac)
        (by rw [hr2]; simp; omega)
      apply WP.spec_mono this
      rintro ⟨r1, b1⟩ hp
      simp only [WP.uncurry'] at hp ⊢
      rw [hp, hr2]
      rcases bulkTypesRead n (List.drop 3 buf.val) with _ | ts
      · rfl
      · simp [hseq1, SBParam.ptOf]

private theorem types_items (n : Usize) (pb : io.ParseBuf)
    (hb : pb.val.length = 3 * n.val) :
    misc.raw.seq.parse_items packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
      packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple n pb
      (alloc.vec.Vec.with_capacity packets.StmtBulkExecuteParamType n) ⦃ r _ =>
      (okPart r).map (fun c => (cowList c).map SBParam.ptOf) = bulkTypesRead n.val pb.val ⦄ := by
  unfold misc.raw.seq.parse_items
  step with types_loop n.val { start := 0#usize, «end» := n } pb
    (alloc.vec.Vec.with_capacity packets.StmtBulkExecuteParamType n) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]; scalar_tac) hb as ⟨ r, rest, h ⟩
  rw [h]
  rcases bulkTypesRead n.val pb.val with _ | ts <;> simp [alloc.vec.Vec.with_capacity]

private theorem parse_types (n : Usize) (hn : 3 * n.val ≤ Usize.max) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize
      packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
      packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize) buf n ⦃ r rest =>
      if 3 * n.val ≤ buf.val.length then
        (okPart r).map (fun s => (cowList s.1).map SBParam.ptOf) = bulkTypesRead n.val (buf.val.take (3 * n.val)) ∧
        rest.val = buf.val.drop (3 * n.val)
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq])]
  let Q : Option (List packets.StmtBulkExecuteParamType) → io.ParseBuf → Prop := fun o rest =>
    if 3 * n.val ≤ buf.val.length then
        o.map (fun s => s.map SBParam.ptOf) = bulkTypesRead n.val (buf.val.take (3 * n.val)) ∧
        rest.val = buf.val.drop (3 * n.val)
      else o = none ∧ rest = buf
  suffices key : misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize
      packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
      packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple n buf ⦃ r rest =>
        Q ((okPart r).map cowList) rest ⦄ by
    have := misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
      packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
      packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize n buf Q key
    apply WP.spec_mono this
    rintro ⟨r, rest⟩ hq
    simp only [WP.uncurry', Q] at hq ⊢
    by_cases hl : 3 * n.val ≤ buf.val.length
    · simp only [hl, ite_true, Option.map_map, Function.comp_def] at hq ⊢; exact hq
    · simp only [hl, ite_false] at hq ⊢
      refine ⟨?_, hq.2⟩
      have := hq.1
      cases hr : okPart r <;> simp_all
  unfold misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize
  simp only [packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq, bind_ok]
  step as ⟨ i, hi ⟩
  step with parse_parsebuf_spec buf i as ⟨ r, buf1, hr ⟩
  rw [hi] at hr
  by_cases hl : 3 * n.val ≤ buf.val.length
  · have hl' : 3 * n.val ≤ Slice.length buf := by simpa [Slice.length] using hl
    simp only [hl', ite_true] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok pb =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      apply spec_bind_ok
      dsimp only
      refine WP.spec_bind (types_items n pb (by rw [hr1]; simp; omega)) (fun q hq => ?_)
      obtain ⟨r1, b1⟩ := q
      simp only [WP.uncurry'] at hq
      apply (WP.spec_ok _).mpr
      simp only [WP.uncurry', Q, hl, ite_true, Option.map_map]
      refine ⟨?_, hr2⟩
      rw [Function.comp_def, hq, hr1]
  · have hl' : ¬ 3 * n.val ≤ Slice.length buf := by simpa [Slice.length] using hl
    simp only [hl', ite_false] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok pb => simp [okPart] at hr1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, hl, Q]

/-! ## The header fields -/

private theorem bulk_try_from (p : U16) :
    constants.StmtBulkExecuteFlags.Insts.CoreConvertTryFromU16UnknownStmtBulkExecuteParamsFlags.try_from p ⦃ r =>
      (okPart r).map (fun c : constants.StmtBulkExecuteFlags => c.val) =
        if p.val &&& 192 = p.val then some p.val else none ⦄ := by
  simp only [constants.StmtBulkExecuteFlags.Insts.CoreConvertTryFromU16UnknownStmtBulkExecuteParamsFlags.try_from,
    constants.StmtBulkExecuteFlags.from_bits, constants.StmtBulkExecuteFlags.from_bits_truncate,
    constants.StmtBulkExecuteFlags.all, lift, bind_ok]
  have h192 : ((0#u16 ||| 64#u16) ||| 128#u16 : U16) = 192#u16 := by decide
  rw [h192]
  by_cases hc : p.val &&& 192 = p.val
  · have : (p &&& 192#u16) = p := by apply UScalar.eq_of_val_eq; simpa using hc
    simp [this, hc, okPart]
  · have : ¬ (p &&& 192#u16) = p := by
      intro h0; apply hc; have := congrArg UScalar.val h0; simpa using this
    simp [this, hc, okPart]

private theorem parse_flags (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      constants.StmtBulkExecuteFlags.Insts.CoreConvertTryFromU16UnknownStmtBulkExecuteParamsFlags
      constants.UnknownStmtBulkExecuteParamsFlags.Insts.CoreErrorError) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (fun c => c.1.val) =
          (if leNat (buf.val.take 2) &&& 192 = leNat (buf.val.take 2) then some (leNat (buf.val.take 2)) else none) ∧
        rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄ := by
  refine IntAndMisc.parse_fixed (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      constants.StmtBulkExecuteFlags.Insts.CoreConvertTryFromU16UnknownStmtBulkExecuteParamsFlags
      constants.UnknownStmtBulkExecuteParamsFlags.Insts.CoreErrorError) 2#usize (by
    simp [misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq,
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq]) buf ()
    (fun o => o.map (fun c => c.1.val) =
      (if leNat (buf.val.take 2) &&& 192 = leNat (buf.val.take 2) then some (leNat (buf.val.take 2)) else none))
    (fun sub hsub hl => ?_)
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
    constants.StmtBulkExecuteFlags.Insts.CoreConvertTryFromU16UnknownStmtBulkExecuteParamsFlags
    constants.UnknownStmtBulkExecuteParamsFlags.Insts.CoreErrorError sub
    (fun o _ => o.map (fun v : U16 => v.val) = some (leNat (buf.val.take 2)))
    (by
      apply WP.spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec sub
        (by simp [Slice.length, hsub] at hl ⊢; omega))
      rintro ⟨r, rest⟩ ⟨h1, -⟩
      simpa [hsub, List.take_take] using h1)
    (fun p o => o.map (fun c : constants.StmtBulkExecuteFlags => c.val) =
        if p.val &&& 192 = p.val then some p.val else none)
    bulk_try_from
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, h1, h2⟩
  cases o with
  | none => simp at h1
  | some p =>
    simp only [Option.map_some, Option.some.injEq] at h1
    simp only [WP.uncurry']
    rw [← h1]
    simpa [Option.map_map, Function.comp_def] using h2

private theorem const_deref_spec {T U : Type} (c : misc.raw._const.Const T U) :
    misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref c ⦃ x => x = c.1 ⦄ := by
  rw [misc.raw._const.Const.deref_eq]; simp

private theorem contains_types (f : constants.StmtBulkExecuteFlags) :
    constants.StmtBulkExecuteFlags.contains f constants.StmtBulkExecuteFlags.SEND_TYPES_TO_SERVER =
      ok (hasFlag f.val SEND_TYPES_TO_SERVER) := by
  simp only [constants.StmtBulkExecuteFlags.contains, constants.StmtBulkExecuteFlags.SEND_TYPES_TO_SERVER,
    hasFlag, SEND_TYPES_TO_SERVER, lift, bind_ok, ok.injEq]
  apply decide_eq_decide.mpr
  constructor
  · intro h0; have := congrArg UScalar.val h0; simpa using this
  · intro h0; apply UScalar.eq_of_val_eq; simpa using h0

private theorem bulkTypeRead_some (bs : List U8) (t : Nat × Nat) (h : (bulkTypeRead bs).1 = some t) :
    (columnTypeOfCode t.1).isSome ∧ (t.2 = 0 ∨ t.2 = 128) := by
  unfold bulkTypeRead at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hn
      split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp only [Option.isNone_iff_eq_none] at hn
          refine ⟨?_, by assumption⟩
          cases hc : columnTypeOfCode _ <;> simp_all
        · simp at h

private theorem bulkTypesRead_props (n : Nat) (bs : List U8) (ts : List (Nat × Nat))
    (h : bulkTypesRead n bs = some ts) :
    ts.length = n ∧ ∀ t ∈ ts, (columnTypeOfCode t.1).isSome ∧ (t.2 = 0 ∨ t.2 = 128) := by
  induction n generalizing bs ts with
  | zero => simp [bulkTypesRead] at h; subst h; simp
  | succ n ih =>
    rw [bulkTypesRead_succ] at h
    rcases h1 : (bulkTypeRead (bs.take 3)).1 with _ | t
    · simp [h1] at h
    · rw [h1] at h
      rcases h2 : bulkTypesRead n (bs.drop 3) with _ | ts'
      · simp [h2] at h
      · simp only [h2, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hall⟩ := ih _ _ h2
        refine ⟨by simp [hl], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact bulkTypeRead_some _ _ h1
        · exact hall x hx

/-! ## Setting the parameter types -/

private def gParam (p : constants.ColumnType × constants.ColumnFlags) : constants.ColumnType × Bool :=
  (p.1, isUnsigned p.2)

private def hType (t : packets.StmtBulkExecuteParamType) : constants.ColumnType × Bool :=
  (t.type.1, decide (t.flags.1.val &&& 128 = 128))

private theorem take_succ_set {α : Type} (l : List α) (k : Nat) (x : α) (hk : k < l.length) :
    (l.set k x).take (k + 1) = l.take k ++ [x] := by
  rw [List.take_add_one, List.take_set_of_le (by omega), List.getElem?_set_self (by omega)]
  simp

private theorem take_succ_set' {α : Type} (l : List α) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp

private theorem isUnsigned_set(cf : constants.ColumnFlags) (b : Bool) (r : constants.ColumnFlags)
    (hr : r.val = if b then cf.val ||| constants.ColumnFlags.UNSIGNED_FLAG.val
      else andNot 16 cf.val constants.ColumnFlags.UNSIGNED_FLAG.val) :
    isUnsigned r = b := by
  unfold isUnsigned
  rw [hr]
  have h32 : constants.ColumnFlags.UNSIGNED_FLAG.val = 32 := by simp [constants.ColumnFlags.UNSIGNED_FLAG]
  cases b <;> simp only [h32, ite_true, Bool.false_eq_true, ite_false, andNot]
  · rw [Nat.testBit_and]; simp [show Nat.testBit 65503 5 = false by decide]
  · rw [Nat.testBit_or]; simp [show Nat.testBit 32 5 = true by decide]

private theorem set_types_spec (types : Slice packets.StmtBulkExecuteParamType)
    (params : Slice (constants.ColumnType × constants.ColumnFlags)) (hl : types.length = params.length) :
    packets.set_bulk_param_types types params ⦃ r =>
      r.val.map gParam = types.val.map hType ⦄ := by
  unfold packets.set_bulk_param_types
  have hn : (if Slice.len types < Slice.len params then ok (Slice.len types) else ok (Slice.len params) :
      Result Usize) = ok (Slice.len types) := by
    split <;> simp_all [Slice.len]
  simp only [hn, bind_ok]
  clear hn
  unfold packets.set_bulk_param_types_loop
  apply loop.spec_decr_nat (fun p => types.length - p.1.start.val)
    (fun p => p.1.end = Slice.len types ∧ p.1.start.val ≤ types.length ∧ p.2.length = types.length ∧
      (p.2.val.take p.1.start.val).map gParam = (types.val.take p.1.start.val).map hType)
  · rintro ⟨it, ps⟩ ⟨h1, h2, h3, h4⟩
    have h1' : it.end = Slice.len types := h1
    have hen : it.end.val = types.length := by rw [h1']; simp
    have h2' : it.start.val ≤ types.length := h2
    have h3' : ps.length = types.length := h3
    have h4' : (ps.val.take it.start.val).map gParam = (types.val.take it.start.val).map hType := h4
    clear h1 h2 h3 h4
    unfold packets.set_bulk_param_types_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hin : it.start.val < types.length := by omega
      have hpin : it.start.val < ps.length := by omega
      step as ⟨t, ht⟩
      obtain ⟨⟨tc, tp⟩, ⟨tfl, tfp⟩⟩ := t
      simp only [misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref]
      have hpin' : it.start.val < ps.val.length := by simpa [Slice.length] using hpin
      have hm : ps.index_mut_usize it.start = ok (ps.val[it.start.val], Slice.set ps it.start) := by
        simp [Slice.index_mut_usize, Slice.index_usize, hpin']
      generalize hp0 : ps.val[it.start.val] = p0 at hm
      obtain ⟨ct0, cf0⟩ := p0
      rw [hm]
      simp only [bind_ok]
      step*
      simp only [Slice.set_val_eq, List.getElem_set_self, Prod.mk.injEq] at ct1_post
      obtain ⟨rfl, rfl⟩ := ct1_post
      subst index_mut_back1_post
      simp only [constants.StmtExecuteParamFlags.contains, lift, bind_ok]
      step with constants.ColumnFlags.set_spec as ⟨cf2, hcf2⟩
      refine ⟨by rw [o_post1, h1'], by omega,
        by simp only [Slice.length, Slice.set_val_eq, List.length_set] at h3' ⊢; exact h3', ?_, by omega⟩
      rw [hi1]
      simp only [Slice.set_val_eq, List.set_set]
      rw [take_succ_set _ _ _ hpin', take_succ_set' types.val it.start.val hin, ← ht]
      simp only [List.map_append, List.map_cons, List.map_nil, h4']
      congr 2
      simp only [gParam, hType, Prod.mk.injEq, true_and]
      rw [isUnsigned_set cf1 _ cf2 hcf2]
      simp only [constants.StmtExecuteParamFlags.UNSIGNED]
      apply decide_eq_decide.mpr
      constructor
      · intro h0; have := congrArg UScalar.val h0; simpa using this
      · intro h0; apply UScalar.eq_of_val_eq; simpa using h0
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      simp only [WP.spec_ok]
      have e1 : ps.val.take it.start.val = ps.val :=
        List.take_of_length_le (by simp only [Slice.length] at h3' hen; omega)
      have e2 : types.val.take it.start.val = types.val :=
        List.take_of_length_le (by simp only [Slice.length] at hen; omega)
      rw [e1, e2] at h4'
      exact h4'
  · exact ⟨rfl, by simp, by simp [Slice.length] at hl ⊢; omega, by simp⟩

private theorem params_eq (s : List packets.StmtBulkExecuteParamType)
    (ps : List (constants.ColumnType × constants.ColumnFlags)) (hset : ps.map gParam = s.map hType)
    (hts : ∀ t ∈ s.map SBParam.ptOf, t.2 = 0 ∨ t.2 = 128) :
    ps.map (fun p => (p.1, isUnsigned p.2)) =
      (s.map SBParam.ptOf).filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, decide (t.2 = 128)))) := by
  have e1 : ps.map (fun p => (p.1, isUnsigned p.2)) = ps.map gParam := rfl
  rw [e1, hset]
  clear hset e1
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h2 := hts (SBParam.ptOf t) (by simp)
    simp only [List.map_cons, List.filterMap_cons, SBParam.ptOf,
      (columnTypeOfCode_columnTypeCode t.type.1).2, Option.map_some]
    rw [ih (fun x hx => hts x (by simp [hx]))]
    simp only [SBParam.ptOf] at h2
    simp only [hType, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    rcases h2 with h2 | h2 <;> rw [h2] <;> simp

private theorem parse_values (h64 : Target64)
    (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (r0 : Option (List (Nat × Val))) (rest0 : List U8)
    (h : bulkValuesRead (bulkParams params) buf.val = .done r0 rest0) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags
      buf params ⦃ r rest => (okPart r).map (fun vs => vs.values.val.map bulkIV) = r0 ∧ rest.val = rest0 ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq])]
  exact packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    h64 params buf r0 rest0 h

private theorem parse_values_panic (h64 : Target64)
    (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (e : Error) (h : bulkValuesRead (bulkParams params) buf.val = .panic e) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags
      buf params = fail e := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq])]
  exact packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    h64 params buf e h

/-- `MyDeserialize for ComStmtBulkExecuteRequest` with the parameters `params` the caller knows:
    exactly `bulkReqRead` whenever that reader returns. **Crate bugs** (see `bulkReqRead`):
    with `SEND_TYPES_TO_SERVER` each type is read from 3 bytes although it is sent in 2, so a
    request with parameters and types is misread (`Defs.bulkReqRead_types_misread`); only the
    first row of values is read (`Defs.bulkReqRead_first_row_only`). Precondition: `3 *
    params.len()` does not overflow `usize` (true of every real `Vec`). -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (r0 : Option BulkReq) (rest0 : List U8)
    (h : bulkReqRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map BulkReq.of = r0 ∧ rest.val = rest0 ⦄ := by
  unfold packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize
  have hd : packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
    simp [packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault.default]
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec 250#u8
    packets.InvalidComStmtBulkExecuteHeader.Insts.CoreErrorError
    packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault hd buf as ⟨r1, b1, P1⟩
  rcases hb : buf.val with _ | ⟨h0, t⟩
  · have hl : ¬ 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    simp only [hl, ite_false] at P1
    obtain ⟨P1a, rfl⟩ := P1
    rw [hb] at h
    simp only [bulkReqRead, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases r1 with
    | Ok _ => simp [okPart] at P1a
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, hb]
  · have hl : 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    simp only [hl, ite_true, hb, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero] at P1
    obtain ⟨P1a, P1b⟩ := P1
    have hleN : leNat [h0] = h0.val := by simp [leNat]
    rw [hb] at h
    simp only [bulkReqRead] at h
    by_cases hh : h0.val = 0xFA
    · obtain ⟨val, rfl⟩ : ∃ v, r1 = .Ok v := by
        cases r1 with
        | Ok v => exact ⟨v, rfl⟩
        | Err _ => simp [okPart, hleN, hh] at P1a
      simp only [hh, ne_eq, not_true_eq_false, ite_false] at h
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec b1 as ⟨r2, b2, P2⟩
      by_cases h4 : t.length < 4
      · have hl2 : ¬ 4 ≤ Slice.length b1 := by simp [Slice.length, P1b]; omega
        simp only [hl2, ite_false] at P2
        obtain ⟨P2a, rfl⟩ := P2
        simp only [h4, ite_true, ReadOut.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases r2 with
        | Ok _ => simp [okPart] at P2a
        | Err e => simp [okPart, P1b]
      · have hl2 : 4 ≤ Slice.length b1 := by simp [Slice.length, P1b]; omega
        simp only [hl2, ite_true, P1b] at P2
        obtain ⟨P2a, P2b⟩ := P2
        obtain ⟨val1, rfl⟩ : ∃ v, r2 = .Ok v := by
          cases r2 with
          | Ok v => exact ⟨v, rfl⟩
          | Err _ => simp [okPart] at P2a
        simp only [okPart, Option.map_some, Option.some.injEq] at P2a
        simp only [h4, ite_false] at h
        step with parse_flags b2 as ⟨r3, b3, P3⟩
        by_cases h6 : t.length < 6
        · have hl3 : ¬ 2 ≤ Slice.length b2 := by simp [Slice.length, P2b]; omega
          simp only [hl3, ite_false] at P3
          obtain ⟨P3a, rfl⟩ := P3
          simp only [h6, ite_true, ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases r3 with
          | Ok _ => simp [okPart] at P3a
          | Err e => simp [okPart, P2b]
        · have hl3 : 2 ≤ Slice.length b2 := by simp [Slice.length, P2b]; omega
          simp only [hl3, ite_true, P2b] at P3
          obtain ⟨P3a, P3b⟩ := P3
          have h192 : SEND_UNIT_RESULTS ||| SEND_TYPES_TO_SERVER = 192 := by decide
          simp only [h6, ite_false, h192] at h
          by_cases hf : leNat ((t.drop 4).take 2) &&& 192 = leNat ((t.drop 4).take 2)
          · obtain ⟨val2, rfl⟩ : ∃ v, r3 = .Ok v := by
              cases r3 with
              | Ok v => exact ⟨v, rfl⟩
              | Err _ => simp [okPart, hf] at P3a
            simp only [okPart, Option.map_some, hf, ite_true, Option.some.injEq] at P3a
            simp only [hf, not_true_eq_false, ite_false] at h
            step with const_deref_spec val2 as ⟨sbef, hsbef⟩
            subst hsbef
            simp only [contains_types, bind_ok]
            rw [P3a]
            have hsl : ((t.drop 4).drop 2) = t.drop 6 := by simp [List.drop_drop]
            rw [hsl] at P3b
            by_cases hft : hasFlag (leNat ((t.drop 4).take 2)) SEND_TYPES_TO_SERVER
            · simp only [hft, ite_true] at h ⊢
              have hlen : (bulkParams params).length = params.val.length := by simp [bulkParams]
              have hn' : 3 * (alloc.vec.Vec.len params).val ≤ Usize.max := by
                simpa [alloc.vec.Vec.len, alloc.vec.Vec.length] using hn
              step with parse_types (alloc.vec.Vec.len params) hn' b3 as ⟨r4, b4, P4⟩
              have hlv : (alloc.vec.Vec.len params).val = params.val.length := by simp [alloc.vec.Vec.len]
              rw [hlv, P3b] at P4
              rw [hlen] at h
              by_cases h3n : (t.drop 6).length < 3 * params.val.length
              · simp only [h3n, ite_true, ReadOut.done.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [show ¬ 3 * params.val.length ≤ (t.drop 6).length by omega, ite_false] at P4
                obtain ⟨P4a, rfl⟩ := P4
                cases r4 with
                | Ok _ => simp [okPart] at P4a
                | Err e => simp [okPart, P3b]
              · simp only [h3n, ite_false] at h
                simp only [show 3 * params.val.length ≤ (t.drop 6).length by omega, ite_true] at P4
                obtain ⟨P4a, P4b⟩ := P4
                cases hts : bulkTypesRead params.val.length ((t.drop 6).take (3 * params.val.length)) with
                | none =>
                  rw [hts] at h P4a
                  simp only [ReadOut.done.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases r4 with
                  | Ok _ => simp [okPart] at P4a
                  | Err e => simp [okPart, P4b]
                | some ts =>
                  rw [hts] at h P4a
                  simp only at h
                  obtain ⟨s, rfl⟩ : ∃ v, r4 = .Ok v := by
                    cases r4 with
                    | Ok v => exact ⟨v, rfl⟩
                    | Err _ => simp [okPart] at P4a
                  simp only [okPart, Option.map_some, Option.some.injEq] at P4a
                  step with misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec _ s as ⟨s1, hs1⟩
                  obtain ⟨hts_len, hts_all⟩ := bulkTypesRead_props _ _ _ hts
                  have hlift : lift (alloc.vec.Vec.deref_mut params) ⦃ p => p = alloc.vec.Vec.deref_mut params ⦄ :=
                    (WP.spec_ok _).mpr rfl
                  step with hlift as ⟨s2, back, hp⟩
                  simp only [alloc.vec.Vec.deref_mut, Prod.mk.injEq] at hp
                  obtain ⟨rfl, rfl⟩ := hp
                  have hs1len : s1.length = params.slice.length := by
                    simp only [Slice.length, hs1]
                    rw [← List.length_map (f := SBParam.ptOf), P4a, hts_len]
                    rfl
                  step with set_types_spec s1 params.slice hs1len as ⟨s3, hs3⟩
                  have hbp : bulkParams { slice := s3 } =
                      ts.filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, decide (t.2 = 128)))) := by
                    unfold bulkParams
                    have := params_eq s1.val s3.val hs3 (by
                      intro x hx
                      rw [hs1, P4a] at hx
                      exact (hts_all x hx).2)
                    rw [hs1, P4a] at this
                    exact this
                  cases hv : bulkValuesRead
                      (ts.filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, decide (t.2 = 128)))))
                      ((t.drop 6).drop (3 * params.val.length)) with
                  | done rv rest =>
                    rw [hv] at h
                    cases rv with
                    | none =>
                      simp only [ReadOut.done.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      step with parse_values h64 { slice := s3 } b4 none rest (by rw [hbp, P4b]; exact hv)
                        as ⟨r5, b5, P5a, P5b⟩
                      cases r5 with
                      | Ok _ => simp [okPart] at P5a
                      | Err e => simp [okPart, P5b]
                    | some vs =>
                      simp only [ReadOut.done.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      step with parse_values h64 { slice := s3 } b4 (some vs) rest (by rw [hbp, P4b]; exact hv)
                        as ⟨r5, b5, P5a, P5b⟩
                      cases r5 with
                      | Err _ => simp [okPart] at P5a
                      | Ok v =>
                        simp only [okPart, Option.map_some, Option.some.injEq] at P5a
                        simp [okPart, P5b, BulkReq.of, P2a, P3a,
                          ← P4a, SBParam.ptOf]
                        exact P5a
                  | panic e => rw [hv] at h; simp at h
                  | unknown => rw [hv] at h; simp at h
            · simp only [hft, Bool.false_eq_true, ite_false] at h ⊢
              have hseq : misc.raw.seq.Seq.new misc.raw.seq.Unknown packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
                  (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
                    packets.StmtBulkExecuteParamType.Insts.CoreCloneClone))
                  (alloc.vec.Vec.new packets.StmtBulkExecuteParamType) ⦃ x => cowList x.1 = [] ⦄ := by
                rw [misc.raw.seq.Seq.new_eq _ _ _ _ (.Owned (alloc.vec.Vec.new packets.StmtBulkExecuteParamType)) (by rfl)]
                exact (WP.spec_ok _).mpr rfl
              step with hseq as ⟨ty, hty⟩
              cases hv : bulkValuesRead (bulkParams params) (t.drop 6) with
              | done rv rest =>
                rw [hv] at h
                cases rv with
                | none =>
                  simp only [ReadOut.done.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  step with parse_values h64 params b3 none rest (by rw [P3b]; exact hv) as ⟨r4, b4, P4a, P4b⟩
                  cases r4 with
                  | Ok _ => simp [okPart] at P4a
                  | Err e => simp [okPart, P4b]
                | some vs =>
                  simp only [ReadOut.done.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  step with parse_values h64 params b3 (some vs) rest (by rw [P3b]; exact hv) as ⟨r4, b4, P4a, P4b⟩
                  cases r4 with
                  | Err _ => simp [okPart] at P4a
                  | Ok v =>
                    simp only [okPart, Option.map_some, Option.some.injEq] at P4a
                    simp [okPart, P4b, BulkReq.of, P2a, P3a, hty]
                    exact P4a
              | panic e => rw [hv] at h; simp at h
              | unknown => rw [hv] at h; simp at h
          · simp only [hf, not_false_eq_true, ite_true, ReadOut.done.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            cases r3 with
            | Ok _ => simp [okPart, hf] at P3a
            | Err e => simp [okPart, P3b, List.drop_drop]
    · simp only [hh, ne_eq, not_false_eq_true, ite_true, ReadOut.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases r1 with
      | Ok _ => simp [okPart, hleN, hh] at P1a
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, P1b]

/-- **Crash path.** `MyDeserialize for ComStmtBulkExecuteRequest` panics where `bulkReqRead` does:
    a value for a parameter whose column type (sent by the client with `SEND_TYPES_TO_SERVER`,
    or known to the caller) the binary reader does not support. A client can thus crash a
    server-side reader. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (e : Error)
    (h : bulkReqRead (bulkParams params) buf.val = .panic e) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e := by
  unfold packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize
  have hd : packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
    simp [packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault.default]
  apply bind_fail_pair (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec 250#u8
    packets.InvalidComStmtBulkExecuteHeader.Insts.CoreErrorError
    packets.InvalidComStmtBulkExecuteHeader.Insts.CoreDefaultDefault hd buf)
  intro r1 b1 P1
  rcases hb : buf.val with _ | ⟨h0, t⟩
  · rw [hb] at h; simp [bulkReqRead] at h
  · have hl : 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    simp only [hl, ite_true, hb, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero] at P1
    obtain ⟨P1a, P1b⟩ := P1
    have hleN : leNat [h0] = h0.val := by simp [leNat]
    rw [hb] at h
    simp only [bulkReqRead] at h
    by_cases hh : h0.val = 0xFA
    · obtain ⟨val, rfl⟩ : ∃ v, r1 = .Ok v := by
        cases r1 with
        | Ok v => exact ⟨v, rfl⟩
        | Err _ => simp [okPart, hleN, hh] at P1a
      simp only [hh, ne_eq, not_true_eq_false, ite_false] at h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      by_cases h4 : t.length < 4
      · simp [h4] at h
      simp only [h4, ite_false] at h
      apply bind_fail_pair (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec b1)
      intro r2 b2 P2
      have hl2 : 4 ≤ Slice.length b1 := by simp [Slice.length, P1b]; omega
      simp only [hl2, ite_true, P1b] at P2
      obtain ⟨P2a, P2b⟩ := P2
      obtain ⟨val1, rfl⟩ : ∃ v, r2 = .Ok v := by
        cases r2 with
        | Ok v => exact ⟨v, rfl⟩
        | Err _ => simp [okPart] at P2a
      simp only [bind_ok]
      by_cases h6 : t.length < 6
      · simp [h6] at h
      simp only [h6, ite_false] at h
      apply bind_fail_pair (parse_flags b2)
      intro r3 b3 P3
      have hl3 : 2 ≤ Slice.length b2 := by simp [Slice.length, P2b]; omega
      simp only [hl3, ite_true, P2b] at P3
      obtain ⟨P3a, P3b⟩ := P3
      have h192 : SEND_UNIT_RESULTS ||| SEND_TYPES_TO_SERVER = 192 := by decide
      simp only [h192] at h
      by_cases hf : leNat ((t.drop 4).take 2) &&& 192 = leNat ((t.drop 4).take 2)
      swap
      · simp [hf] at h
      obtain ⟨val2, rfl⟩ : ∃ v, r3 = .Ok v := by
        cases r3 with
        | Ok v => exact ⟨v, rfl⟩
        | Err _ => simp [okPart, hf] at P3a
      simp only [okPart, Option.map_some, hf, ite_true, Option.some.injEq] at P3a
      simp only [hf, not_true_eq_false, ite_false] at h
      simp only [bind_ok]
      apply PBUtil.bind_fail_of_spec (const_deref_spec val2)
      rintro sbef rfl
      simp only [contains_types, bind_ok]
      rw [P3a]
      have hsl : ((t.drop 4).drop 2) = t.drop 6 := by simp [List.drop_drop]
      rw [hsl] at P3b
      by_cases hft : hasFlag (leNat ((t.drop 4).take 2)) SEND_TYPES_TO_SERVER
      · simp only [hft, ite_true] at h ⊢
        have hlen : (bulkParams params).length = params.val.length := by simp [bulkParams]
        have hn' : 3 * (alloc.vec.Vec.len params).val ≤ Usize.max := by
          simpa [alloc.vec.Vec.len, alloc.vec.Vec.length] using hn
        apply bind_fail_pair (parse_types (alloc.vec.Vec.len params) hn' b3)
        intro r4 b4 P4
        have hlv : (alloc.vec.Vec.len params).val = params.val.length := by simp [alloc.vec.Vec.len]
        rw [hlv, P3b] at P4
        rw [hlen] at h
        by_cases h3n : (t.drop 6).length < 3 * params.val.length
        · simp only [h3n, ite_true] at h; simp at h
        simp only [h3n, ite_false] at h
        simp only [show 3 * params.val.length ≤ (t.drop 6).length by omega, ite_true] at P4
        obtain ⟨P4a, P4b⟩ := P4
        cases hts : bulkTypesRead params.val.length ((t.drop 6).take (3 * params.val.length)) with
        | none => rw [hts] at h; simp at h
        | some ts =>
          rw [hts] at h P4a
          simp only at h
          obtain ⟨s, rfl⟩ : ∃ v, r4 = .Ok v := by
            cases r4 with
            | Ok v => exact ⟨v, rfl⟩
            | Err _ => simp [okPart] at P4a
          simp only [okPart, Option.map_some, Option.some.injEq] at P4a
          simp only [bind_ok]
          apply PBUtil.bind_fail_of_spec (misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec _ s)
          intro s1 hs1
          obtain ⟨hts_len, _⟩ := bulkTypesRead_props _ _ _ hts
          have hlift : lift (alloc.vec.Vec.deref_mut params) ⦃ a b =>
              a = params.slice ∧ b = (fun s => ({ slice := s } : alloc.vec.Vec _)) ⦄ :=
            (WP.spec_ok _).mpr ⟨rfl, rfl⟩
          apply bind_fail_pair hlift
          intro s2 back hp
          obtain ⟨rfl, rfl⟩ := hp
          have hs1len : s1.length = params.slice.length := by
            simp only [Slice.length, hs1]
            rw [← List.length_map (f := SBParam.ptOf), P4a, hts_len]
            rfl
          apply PBUtil.bind_fail_of_spec (set_types_spec s1 params.slice hs1len)
          intro s3 hs3
          obtain ⟨_, hts_all⟩ := bulkTypesRead_props _ _ _ hts
          have hbp : bulkParams { slice := s3 } =
              ts.filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, decide (t.2 = 128)))) := by
            unfold bulkParams
            have := params_eq s1.val s3.val hs3 (by
              intro x hx
              rw [hs1, P4a] at hx
              exact (hts_all x hx).2)
            rw [hs1, P4a] at this
            exact this
          cases hv : bulkValuesRead
              (ts.filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, decide (t.2 = 128)))))
              ((t.drop 6).drop (3 * params.val.length)) with
          | panic e' =>
            rw [hv] at h
            simp only [ReadOut.panic.injEq] at h
            subst h
            rw [parse_values_panic h64 { slice := s3 } b4 e' (by rw [hbp, P4b]; exact hv)]
            exact Std.bind_tc_fail _ _
          | done rv rest => rw [hv] at h; cases rv <;> simp at h
          | unknown => rw [hv] at h; simp at h
      · simp only [hft, Bool.false_eq_true, ite_false] at h ⊢
        have hseq : misc.raw.seq.Seq.new misc.raw.seq.Unknown packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
            (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
              packets.StmtBulkExecuteParamType.Insts.CoreCloneClone))
            (alloc.vec.Vec.new packets.StmtBulkExecuteParamType) ⦃ _ => True ⦄ := by
          rw [misc.raw.seq.Seq.new_eq _ _ _ _ (.Owned (alloc.vec.Vec.new packets.StmtBulkExecuteParamType)) (by rfl)]
          exact (WP.spec_ok _).mpr trivial
        apply PBUtil.bind_fail_of_spec hseq
        intro ty _
        cases hv : bulkValuesRead (bulkParams params) (t.drop 6) with
        | panic e' =>
          rw [hv] at h
          simp only [ReadOut.panic.injEq] at h
          subst h
          rw [parse_values_panic h64 params b3 e' (by rw [P3b]; exact hv)]
          exact Std.bind_tc_fail _ _
        | done rv rest => rw [hv] at h; cases rv <;> simp at h
        | unknown => rw [hv] at h; simp at h
    · simp [hh] at h

/-- `MySerialize for ComStmtBulkExecuteRequest`: appends `bulkReqEnc` (header, statement id,
    flags, the types only with `SEND_TYPES_TO_SERVER`, the values). For a request made by `new`
    this is the protocol's packet when every parameter's values have one type (or are `NULL`);
    otherwise each value is encoded in its own type under the merged type (`bulkTypes`, the
    first row's type for conflicting types: the `TODO`), which the server misreads. -/
theorem packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtBulkExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkReqEnc (BulkReq.of self)).length ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkReqEnc (BulkReq.of self) ⦄ := by
  obtain ⟨hdr, sid, fl, ty, vs⟩ := self
  unfold packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [BulkReq.of, bulkReqEnc, List.length_cons, List.length_append, alloc.vec.Vec.length] at h ⊢
  have hl4 := PBUtil.length_leBytes 4 sid.1.val
  have hl2 := PBUtil.length_leBytes 2 fl.1.val
  apply WP.spec_bind (PCSUtil.constu8_serialize hdr buf (by simp only [alloc.vec.Vec.length]; omega))
  intro b1 hb1
  apply WP.spec_bind (PCSUtil.rawint_u32_serialize sid b1
    (by simp only [alloc.vec.Vec.length, hb1, List.length_append, List.length_singleton]; omega))
  intro b2 hb2
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ fl.1 rfl]
  apply WP.spec_bind (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ b2
    (by simp only [alloc.vec.Vec.length, hb1, hb2, List.length_append, List.length_singleton]; omega))
  intro b3 hb3
  have hc : constants.StmtBulkExecuteFlags.contains fl.1 constants.StmtBulkExecuteFlags.SEND_TYPES_TO_SERVER =
      ok (hasFlag fl.1.val SEND_TYPES_TO_SERVER) := by
    simp only [constants.StmtBulkExecuteFlags.contains, constants.StmtBulkExecuteFlags.SEND_TYPES_TO_SERVER,
      hasFlag, SEND_TYPES_TO_SERVER, lift, bind_ok, ok.injEq]
    apply decide_eq_decide.mpr
    constructor
    · intro h0; have := congrArg UScalar.val h0; simpa using this
    · intro h0; apply UScalar.eq_of_val_eq; simpa using h0
  have hd : misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref fl = ok fl.1 := rfl
  rw [hd]
  simp only [bind_ok, hc]
  have hfa : (250#u8 : U8) = byte 0xFA := by decide
  have hiv : (fun v : packets.StmtBulkExecuteParamValue =>
      (bulkIndicatorCode v.indicator.1, Val.ofValue v.value)) = bulkIV := rfl
  rw [hiv] at h ⊢
  have hb3l : b3.val.length = buf.val.length + 7 := by
    simp only [hb3, hb2, hb1, List.length_append, List.length_singleton]; omega
  split
  · rename_i hft
    simp only [hft, ite_true] at h ⊢
    apply WP.spec_bind (misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec _ _ _ ty b3
      (fun b => b.val = b3.val ++ List.flatMap bulkTypeEnc
        (List.map (fun t => (columnTypeCode t.type.1, t.flags.1.val)) (cowList ty.1))) (fun s hs => ?_))
    · intro b4 hb4
      apply WP.spec_mono (packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec vs b4
        (by simp only [alloc.vec.Vec.length, hb4, List.length_append] at h hb3l ⊢; omega))
      intro b5 hb5
      rw [hb5, hb4, hb3, hb2, hb1, hfa]
      simp
    · have := misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_spec
        packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize
        (fun t => bulkTypeEnc (columnTypeCode t.type.1, t.flags.1.val)) s
        (fun x _ b hb => packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize_spec x b
          (by simpa [bulkTypeEnc] using hb)) b3
        (by simp only [alloc.vec.Vec.length]; rw [hs, hb3l]; simp only [List.flatMap_map] at h ⊢; omega)
      rw [hs] at this
      simpa [List.flatMap_map] using this
  · rename_i hft
    simp only [hft] at h ⊢
    apply WP.spec_mono (packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec vs b3
      (by simp only [alloc.vec.Vec.length]; omega))
    intro b5 hb5
    rw [hb5, hb3, hb2, hb1, hfa]
    simp

/-! ## `new`: merging the parameter types -/

private theorem coltype_eq_spec (a b : constants.ColumnType) :
    constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq a b ⦃ r => r ↔ a = b ⦄ := by
  unfold constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq
  simp only [WP.spec_ok, decide_eq_true_eq]
  constructor
  · intro h
    have ha : U8.Insts.CoreConvertFromColumnType.from a = ok (UScalar.cast .U8 (read_discriminant a)) := rfl
    have hb : U8.Insts.CoreConvertFromColumnType.from b = ok (UScalar.cast .U8 (read_discriminant b)) := rfl
    obtain ⟨pa, hpa, hpav⟩ := PBUtil.spec_eq_ok (U8.Insts.CoreConvertFromColumnType.from_spec a)
    obtain ⟨pb, hpb, hpbv⟩ := PBUtil.spec_eq_ok (U8.Insts.CoreConvertFromColumnType.from_spec b)
    rw [ha] at hpa
    rw [hb] at hpb
    simp only [ok.injEq] at hpa hpb
    have hc : columnTypeCode a = columnTypeCode b := by
      rw [← hpav, ← hpbv, ← hpa, ← hpb]; exact congrArg (fun x => (UScalar.cast UScalarTy.U8 x).val) h
    have h1 := (columnTypeOfCode_columnTypeCode a).2
    rw [hc, (columnTypeOfCode_columnTypeCode b).2] at h1
    exact (Option.some.inj h1).symm
  · rintro rfl; rfl

private theorem code_inj {a b : constants.ColumnType} (h : columnTypeCode a = columnTypeCode b) : a = b := by
  have h1 := (columnTypeOfCode_columnTypeCode a).2
  rw [h, (columnTypeOfCode_columnTypeCode b).2] at h1
  exact (Option.some.inj h1).symm

private theorem merge_step (ts types row : List packets.StmtBulkExecuteParamType) (k : Nat)
    (hk : k < types.length) (hlen : ts.length = types.length) (hrow : types.length ≤ row.length)
    (htake : (ts.take k).map SBParam.ptOf =
      (List.zipWith bulkMerge (types.map SBParam.ptOf) (row.map SBParam.ptOf)).take k)
    (hdrop : ts.drop k = types.drop k) (x : packets.StmtBulkExecuteParamType)
    (hx : SBParam.ptOf x = bulkMerge (SBParam.ptOf types[k]) (SBParam.ptOf (row[k]'(by omega)))) :
    (ts.set k x).length = types.length ∧
    ((ts.set k x).take (k + 1)).map SBParam.ptOf =
      (List.zipWith bulkMerge (types.map SBParam.ptOf) (row.map SBParam.ptOf)).take (k + 1) ∧
    (ts.set k x).drop (k + 1) = types.drop (k + 1) := by
  refine ⟨by simp [hlen], ?_, ?_⟩
  · rw [take_succ_set _ _ _ (by omega), List.map_append, htake]
    have hzl : k < (List.zipWith bulkMerge (types.map SBParam.ptOf) (row.map SBParam.ptOf)).length := by
      simp; omega
    rw [take_succ_set' _ _ hzl]
    simp [hx]
  · rw [List.drop_set_of_lt (by omega)]
    have := congrArg (List.drop 1) hdrop
    simpa [List.drop_drop, Nat.add_comm] using this

@[local step] private theorem coltype_eq_step (a b : constants.ColumnType) :
    constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq a b ⦃ r => r ↔ a = b ⦄ := coltype_eq_spec a b

@[local step] private theorem coltype_get_step (t : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.column_type t ⦃ c => c = t.type.1 ⦄ := by
  rw [packets.StmtBulkExecuteParamType.column_type_eq]; exact (WP.spec_ok _).mpr rfl

@[local step] private theorem pflags_get_step (t : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.impl.flags t ⦃ c => c = t.flags.1 ⦄ := by
  rw [packets.StmtBulkExecuteParamType.impl.flags_eq]; exact (WP.spec_ok _).mpr rfl

@[local step] private theorem pflags_eq_step (a b : constants.StmtExecuteParamFlags) :
    constants.StmtExecuteParamFlags.Insts.CoreCmpPartialEqStmtExecuteParamFlags.eq a b ⦃ r => r ↔ a = b ⦄ := by
  simp [constants.StmtExecuteParamFlags.Insts.CoreCmpPartialEqStmtExecuteParamFlags.eq]

@[local step] private theorem pflags_union_step (a b : constants.StmtExecuteParamFlags) :
    constants.StmtExecuteParamFlags.union a b ⦃ r => r.val = a.val ||| b.val ⦄ := by
  simp [constants.StmtExecuteParamFlags.union, lift]

@[local step] private theorem ptype_new_step (c : constants.ColumnType) (f : constants.StmtExecuteParamFlags) :
    packets.StmtBulkExecuteParamType.new c f ⦃ t => SBParam.ptOf t = (columnTypeCode c, f.val) ⦄ := by
  rw [packets.StmtBulkExecuteParamType.new_eq]; exact (WP.spec_ok _).mpr rfl

open Classical in
private theorem merge_pt (c c' : constants.ColumnType) (f f' : constants.StmtExecuteParamFlags) :
    bulkMerge (columnTypeCode c, f.val) (columnTypeCode c', f'.val) =
      if c ≠ c' then (if c = constants.ColumnType.MYSQL_TYPE_NULL then (columnTypeCode c', f'.val)
        else (columnTypeCode c, f.val))
      else if f ≠ f' then (if c = constants.ColumnType.MYSQL_TYPE_NULL then (columnTypeCode c', f'.val)
        else (columnTypeCode c', f.val ||| f'.val))
      else (columnTypeCode c, f.val) := by
  unfold bulkMerge
  by_cases hc : c = c'
  · subst hc
    by_cases hf : f = f'
    · subst hf; simp
    · have hfv : f.val ≠ f'.val := fun h => hf (UScalar.eq_of_val_eq h)
      by_cases hn : c = constants.ColumnType.MYSQL_TYPE_NULL
      · subst hn; simp [hfv, hf]
      · have : columnTypeCode c ≠ columnTypeCode constants.ColumnType.MYSQL_TYPE_NULL :=
          fun h => hn (code_inj h)
        simp [hfv, hf, hn, this]
  · have hcc : columnTypeCode c ≠ columnTypeCode c' := fun h => hc (code_inj h)
    by_cases hn : c = constants.ColumnType.MYSQL_TYPE_NULL
    · subst hn; simp [hcc, hc]
    · have : columnTypeCode c ≠ columnTypeCode constants.ColumnType.MYSQL_TYPE_NULL :=
        fun h => hn (code_inj h)
      simp [hcc, hc, hn, this]

private theorem get_of_drop {α : Type} (l1 l2 : List α) (k : Nat) (h : l1.drop k = l2.drop k)
    (h1 : k < l1.length) (h2 : k < l2.length) : l1[k] = l2[k] := by
  have := congrArg (fun l => l[0]?) h
  simp only [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  exact Option.some.inj this

private theorem merge_loop (types row : Slice packets.StmtBulkExecuteParamType)
    (hrow : types.length ≤ row.length) (it : core.ops.range.Range Usize)
    (ts : Slice packets.StmtBulkExecuteParamType)
    (he : it.end = Slice.len types) (hs : it.start.val ≤ types.length) (hlen : ts.length = types.length)
    (htake : (ts.val.take it.start.val).map SBParam.ptOf =
      (List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf)).take it.start.val)
    (hdrop : ts.val.drop it.start.val = types.val.drop it.start.val) :
    packets.merge_bulk_param_types_loop it ts row ⦃ r =>
      r.val.map SBParam.ptOf = List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf) ⦄ := by
  unfold packets.merge_bulk_param_types_loop
  apply loop.spec_decr_nat (fun p => types.length - p.1.start.val)
    (fun p => p.1.end = Slice.len types ∧ p.1.start.val ≤ types.length ∧ p.2.length = types.length ∧
      (p.2.val.take p.1.start.val).map SBParam.ptOf =
        (List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf)).take p.1.start.val ∧
      p.2.val.drop p.1.start.val = types.val.drop p.1.start.val)
  · rintro ⟨it, ts⟩ ⟨h1, h2, h3, h4, h5⟩
    have h1' : it.end = Slice.len types := h1
    have hen : it.end.val = types.length := by rw [h1']; simp
    have h2' : it.start.val ≤ types.length := h2
    have h3' : ts.length = types.length := h3
    have h4' := h4
    have h5' : ts.val.drop it.start.val = types.val.drop it.start.val := h5
    clear h1 h2 h3 h4 h5
    unfold packets.merge_bulk_param_types_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hk : it.start.val < types.val.length := by simp only [Slice.length] at hen; omega
      have hkt : it.start.val < ts.val.length := by simp only [Slice.length] at h3' hen; omega
      have hkr : it.start.val < row.val.length := by simp only [Slice.length] at hrow hen; omega
      have hlt : ts.val[it.start.val] = types.val[it.start.val] := get_of_drop _ _ _ h5' hkt hk
      have fin : ∀ (x : packets.StmtBulkExecuteParamType) (s' : Slice packets.StmtBulkExecuteParamType),
          s'.val = ts.val.set it.start.val x →
          SBParam.ptOf x = bulkMerge (SBParam.ptOf ts.val[it.start.val]) (SBParam.ptOf row.val[it.start.val]) →
          (iter1.end = Slice.len types ∧ iter1.start.val ≤ types.length ∧ s'.length = types.length ∧
            (s'.val.take iter1.start.val).map SBParam.ptOf =
              (List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf)).take iter1.start.val ∧
            s'.val.drop iter1.start.val = types.val.drop iter1.start.val ∧
            types.length - iter1.start.val < types.length - it.start.val) := by
        intro x s' hs' hx
        rw [hlt] at hx
        obtain ⟨m1, m2, m3⟩ := merge_step ts.val types.val row.val it.start.val hk
          (by simpa [Slice.length] using h3') (by simpa [Slice.length] using hrow) h4' h5' x hx
        refine ⟨by rw [o_post1, h1'], by omega, ?_, ?_, ?_, by omega⟩
        · simp only [Slice.length, hs']; simpa [Slice.length] using m1
        · rw [hs', hi1]; exact m2
        · rw [hs', hi1]; exact m3
      unfold core.cmp.PartialEq.ne.trait_default
      step*
      · exact coltype_eq_spec _ _
      · apply fin right s (by rw [s_post]; simp)
        subst left_post right_post ct_post ct1_post
        simp only [SBParam.ptOf]
        rw [merge_pt, ite_eq_left (b_post.mp ‹b = true›), ite_eq_left (b1_post.mp ‹b1 = true›)]
      · apply fin ts.val[it.start.val] ts (List.set_getElem_self _).symm
        subst left_post right_post ct_post ct1_post
        simp only [SBParam.ptOf]
        rw [merge_pt, ite_eq_left (b_post.mp ‹b = true›), ite_eq_right (fun h => ‹¬ b1 = true› (b1_post.mpr h))]
      · exact pflags_eq_step _ _
      · apply fin right s (by rw [s_post]; simp)
        subst left_post right_post ct_post ct1_post sepf_post sepf1_post
        simp only [SBParam.ptOf]
        rw [merge_pt, ite_eq_right (fun h => ‹¬ b = true› (b_post.mpr h)), ite_eq_left (b1_post.mp ‹b1 = true›),
          ite_eq_left (b2_post.mp ‹b2 = true›)]
      · apply fin sbept s (by rw [s_post]; simp)
        subst left_post right_post ct_post ct1_post sepf_post sepf1_post
        rw [sbept_post]
        simp only [SBParam.ptOf]
        rw [merge_pt, ite_eq_right (fun h => ‹¬ b = true› (b_post.mpr h)), ite_eq_left (b1_post.mp ‹b1 = true›),
          ite_eq_right (fun h => ‹¬ b2 = true› (b2_post.mpr h)), sepf2_post]
      · apply fin ts.val[it.start.val] ts (List.set_getElem_self _).symm
        subst left_post right_post ct_post ct1_post sepf_post sepf1_post
        simp only [SBParam.ptOf]
        rw [merge_pt, ite_eq_right (fun h => ‹¬ b = true› (b_post.mpr h)),
          ite_eq_right (fun h => ‹¬ b1 = true› (b1_post.mpr h))]
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      simp only [WP.spec_ok]
      have e1 : ts.val.take it.start.val = ts.val :=
        List.take_of_length_le (by simp only [Slice.length] at h3' hen; omega)
      have e2 : (List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf)).take it.start.val =
          List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf) :=
        List.take_of_length_le (by simp only [Slice.length] at hen hrow ⊢; simp; omega)
      rw [e1, e2] at h4'
      exact h4'
  · exact ⟨he, hs, hlen, htake, hdrop⟩

private theorem merge_spec (types row : Slice packets.StmtBulkExecuteParamType)
    (hrow : types.length ≤ row.length) :
    packets.merge_bulk_param_types types row ⦃ r =>
      r.val.map SBParam.ptOf = List.zipWith bulkMerge (types.val.map SBParam.ptOf) (row.val.map SBParam.ptOf) ⦄ := by
  unfold packets.merge_bulk_param_types
  have hn : (if Slice.len types < Slice.len row then ok (Slice.len types) else ok (Slice.len row) :
      Result Usize) = ok (Slice.len types) := by
    split
    · rfl
    · rename_i h
      congr 1
      apply UScalar.eq_of_val_eq
      simp [Slice.len, Slice.length] at h hrow ⊢
      omega
  simp only [hn, bind_ok]
  exact merge_loop types row hrow _ types rfl (by simp) rfl (by simp) (by simp)

private theorem ptypes_loop (row : Slice value.Value) (it : core.ops.range.Range Usize)
    (out : alloc.vec.Vec packets.StmtBulkExecuteParamType)
    (he : it.end = Slice.len row) (hs : it.start.val ≤ row.length)
    (hout : out.val.map SBParam.ptOf = (row.val.take it.start.val).map (fun v => bulkTy (Val.ofValue v)))
    (hcap : out.length + (row.length - it.start.val) ≤ Usize.max) :
    packets.bulk_param_types_loop it row out ⦃ r =>
      r.val.map SBParam.ptOf = row.val.map (fun v => bulkTy (Val.ofValue v)) ⦄ := by
  unfold packets.bulk_param_types_loop
  apply loop.spec_decr_nat (fun p => row.length - p.1.start.val)
    (fun p => p.1.end = Slice.len row ∧ p.1.start.val ≤ row.length ∧
      p.2.val.map SBParam.ptOf = (row.val.take p.1.start.val).map (fun v => bulkTy (Val.ofValue v)) ∧
      p.2.length + (row.length - p.1.start.val) ≤ Usize.max)
  · rintro ⟨it, o⟩ ⟨h1, h2, h3, h4⟩
    have h1' : it.end = Slice.len row := h1
    have hen : it.end.val = row.length := by rw [h1']; simp
    have h2' : it.start.val ≤ row.length := h2
    have h3' : o.val.map SBParam.ptOf = (row.val.take it.start.val).map (fun v => bulkTy (Val.ofValue v)) := h3
    have h4' : o.length + (row.length - it.start.val) ≤ Usize.max := h4
    clear h1 h2 h3 h4
    unfold packets.bulk_param_types_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hk : it.start.val < row.val.length := by simp only [Slice.length] at hen; omega
      step as ⟨v, hv⟩
      step with packets.StmtBulkExecuteParamType.from_value_spec v as ⟨t, ht⟩
      step with alloc.vec.Vec.push_spec o t
        (by simp only [alloc.vec.Vec.length, Slice.length] at h4' hen hc ⊢; omega) as ⟨o1, ho1⟩
      refine ⟨by rw [o_post1, h1'], by omega, ?_, ?_, by omega⟩
      · rw [ho1, hi1, take_succ_set' _ _ hk, List.map_append, List.map_append, h3']
        simp only [List.map_cons, List.map_nil]
        rw [← hv]
        exact congrArg (fun x => _ ++ [x]) ht
      · simp [alloc.vec.Vec.length, ho1] at h4' ⊢; omega
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      simp only [WP.spec_ok]
      rw [h3', List.take_of_length_le (by simp only [Slice.length] at hen; omega)]
  · exact ⟨he, hs, hout, hcap⟩

private theorem ptypes_spec (row : Slice value.Value) :
    packets.bulk_param_types row ⦃ r =>
      r.val.map SBParam.ptOf = row.val.map (fun v => bulkTy (Val.ofValue v)) ⦄ := by
  unfold packets.bulk_param_types
  exact ptypes_loop row _ _ rfl (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length])

private abbrev ivOf (v : value.Value) : Nat × Val := (bulkInd (Val.ofValue v), Val.ofValue v)

private theorem take_row_loop_spec (row0 : Slice value.Value) (out0 : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hmax : out0.val.length + row0.val.length ≤ Usize.max)
    (k : Usize) (row : Slice value.Value) (out : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hk : k.val ≤ row0.val.length) (hrl : row.val.length = row0.val.length) (hrd : row.val.drop k.val = row0.val.drop k.val)
    (ho : out.val.map bulkIV = out0.val.map bulkIV ++ (row0.val.take k.val).map ivOf)
    (hol : out.val.length = out0.val.length + k.val) :
    packets.take_bulk_param_row_loop { start := k, «end» := Slice.len row0 } row out ⦃ r =>
      r.2.val.map bulkIV = out0.val.map bulkIV ++ row0.val.map ivOf ∧ r.2.val.length = out0.val.length + row0.val.length ∧
      r.1.val.length = row0.val.length ⦄ := by
  unfold packets.take_bulk_param_row_loop
  apply loop.spec_decr_nat (fun p => row0.val.length - p.1.start.val)
    (fun p => p.1.end = Slice.len row0 ∧ p.1.start.val ≤ row0.val.length ∧ p.2.1.val.length = row0.val.length ∧
      p.2.1.val.drop p.1.start.val = row0.val.drop p.1.start.val ∧
      p.2.2.val.map bulkIV = out0.val.map bulkIV ++ (row0.val.take p.1.start.val).map ivOf ∧
      p.2.2.val.length = out0.val.length + p.1.start.val)
  · rintro ⟨it, r, o⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    have h1' : it.end = Slice.len row0 := h1
    have hen : it.end.val = row0.val.length := by rw [h1']; simp
    have h2' : it.start.val ≤ row0.val.length := h2
    have h3' : r.val.length = row0.val.length := h3
    have h4' : r.val.drop it.start.val = row0.val.drop it.start.val := h4
    have h5' : o.val.map bulkIV = out0.val.map bulkIV ++ (row0.val.take it.start.val).map ivOf := h5
    have h6' : o.val.length = out0.val.length + it.start.val := h6
    clear h1 h2 h3 h4 h5 h6
    unfold packets.take_bulk_param_row_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hin : it.start.val < row0.val.length := by omega
      have hrin : it.start.val < r.val.length := by omega
      have hget : r.val[it.start.val] = row0.val[it.start.val] := by
        have := congrArg (fun l => l[0]?) h4'
        simp only [List.getElem?_drop, Nat.add_zero] at this
        rw [List.getElem?_eq_getElem hrin, List.getElem?_eq_getElem hin] at this
        exact Option.some.inj this
      step*
      step with packets.StmtBulkExecuteParamValue.new_spec v as ⟨sbepv, hsv, hsi⟩
      step*
      · refine ⟨by rw [o_post1, h1'], by omega, by rw [index_mut_back_post]; simp [h3'], ?_, ?_, ?_, by omega⟩
        · rw [hi1, index_mut_back_post]
          simp only [Slice.set_val_eq]
          rw [List.drop_set_of_lt (by omega)]
          have := congrArg (List.drop 1) h4'
          simpa [List.drop_drop, Nat.add_comm] using this
        · rw [hi1, out1_post, List.map_append, h5', List.take_add_one,
            List.getElem?_eq_getElem hin]
          simp only [List.map_append, Option.toList_some, List.map_cons, List.map_nil, List.append_assoc]
          congr 2
          simp only [bulkIV, ivOf, hsv, hsi, v_post, hget]
        · rw [hi1, out1_post]; simp [h6']; omega
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      simp only [WP.spec_ok]
      have heq : it.start.val = row0.val.length := by omega
      rw [heq] at h5' h6'
      refine ⟨?_, ?_, h3'⟩
      · rw [h5']; simp
      · exact h6'
  · exact ⟨rfl, hk, hrl, hrd, ho, hol⟩

private theorem take_row_spec (row0 : Slice value.Value) (out0 : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hmax : out0.val.length + row0.val.length ≤ Usize.max) :
    packets.take_bulk_param_row row0 out0 ⦃ r =>
      r.2.val.map bulkIV = out0.val.map bulkIV ++ row0.val.map ivOf ∧
      r.2.val.length = out0.val.length + row0.val.length ∧ r.1.val.length = row0.val.length ⦄ := by
  unfold packets.take_bulk_param_row
  exact take_row_loop_spec row0 out0 hmax 0#usize row0 out0 (by simp) rfl rfl (by simp) (by simp)

private theorem take_values_loop_spec (vs0 : Slice (alloc.vec.Vec value.Value))
    (hmax : (vs0.val.map (·.val.length)).sum ≤ Usize.max)
    (k : Usize) (vs : Slice (alloc.vec.Vec value.Value)) (out : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hk : k.val ≤ vs0.val.length) (hrl : vs.val.length = vs0.val.length)
    (hrd : vs.val.drop k.val = vs0.val.drop k.val)
    (ho : out.val.map bulkIV = (vs0.val.take k.val).flatMap (fun r => r.val.map ivOf))
    (hol : out.val.length = ((vs0.val.map (·.val.length)).take k.val).sum) :
    packets.take_bulk_param_values_loop { start := k, «end» := Slice.len vs0 } vs out ⦃ r =>
      r.1.val.map bulkIV = vs0.val.flatMap (fun r => r.val.map ivOf) ⦄ := by
  unfold packets.take_bulk_param_values_loop
  apply loop.spec_decr_nat (fun p => vs0.val.length - p.1.start.val)
    (fun p => p.1.end = Slice.len vs0 ∧ p.1.start.val ≤ vs0.val.length ∧ p.2.1.val.length = vs0.val.length ∧
      p.2.1.val.drop p.1.start.val = vs0.val.drop p.1.start.val ∧
      p.2.2.val.map bulkIV = (vs0.val.take p.1.start.val).flatMap (fun r => r.val.map ivOf) ∧
      p.2.2.val.length = ((vs0.val.map (·.val.length)).take p.1.start.val).sum)
  · rintro ⟨it, r, o⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    have h1' : it.end = Slice.len vs0 := h1
    have hen : it.end.val = vs0.val.length := by rw [h1']; simp
    have h2' : it.start.val ≤ vs0.val.length := h2
    have h3' : r.val.length = vs0.val.length := h3
    have h4' : r.val.drop it.start.val = vs0.val.drop it.start.val := h4
    have h5' : o.val.map bulkIV = (vs0.val.take it.start.val).flatMap (fun r => r.val.map ivOf) := h5
    have h6' : o.val.length = ((vs0.val.map (·.val.length)).take it.start.val).sum := h6
    clear h1 h2 h3 h4 h5 h6
    unfold packets.take_bulk_param_values_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hin : it.start.val < vs0.val.length := by omega
      have hrin : it.start.val < r.val.length := by omega
      have hget : r.val[it.start.val] = vs0.val[it.start.val] := by
        have := congrArg (fun l => l[0]?) h4'
        simp only [List.getElem?_drop, Nat.add_zero] at this
        rw [List.getElem?_eq_getElem hrin, List.getElem?_eq_getElem hin] at this
        exact Option.some.inj this
      have hLin : it.start.val < (vs0.val.map (·.val.length)).length := by simp; omega
      have hs1 := sum_take_succ (vs0.val.map (·.val.length)) it.start.val hLin
      have hs2 := sum_take_le (vs0.val.map (·.val.length)) (it.start.val + 1)
      step*
      have hlift : lift (alloc.vec.Vec.deref_mut v) ⦃ a b =>
          a = v.slice ∧ b = (fun s => ({ slice := s } : alloc.vec.Vec _)) ⦄ := (WP.spec_ok _).mpr ⟨rfl, rfl⟩
      step with hlift as ⟨sl, back, hsl⟩
      obtain ⟨rfl, rfl⟩ := hsl
      have hrow_eq : v.slice.val = (vs0.val[it.start.val]).val := by rw [v_post, hget]; rfl
      have hlen_k : (vs0.val[it.start.val]).val.length = (List.map (fun x => x.val.length) vs0.val)[it.start.val] := by
        simp
      step with take_row_spec v.slice o (by
          simp only [hrow_eq, h6']; rw [hlen_k, ← hs1]; omega)
        as ⟨s1, out1, hq1, hq2, hq3⟩
      subst index_mut_back_post
      refine ⟨by rw [o_post1, h1'], by omega, by simp [h3'], ?_, ?_, ?_, by omega⟩
      · rw [Slice.set_val_eq, List.drop_set_of_lt (by omega), hi1]
        have := congrArg (List.drop 1) h4'
        simpa [List.drop_drop, Nat.add_comm] using this
      · rw [hq1, h5', hi1, take_succ_set' _ _ hin, List.flatMap_append, hrow_eq]
        simp
      · rw [hi1, hs1, ← hlen_k, ← hrow_eq, ← h6']
        omega
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      simp only [WP.spec_ok]
      have heq : it.start.val = vs0.val.length := by omega
      rw [heq] at h5'
      rw [h5']; simp
  · exact ⟨rfl, hk, hrl, hrd, ho, hol⟩

private theorem take_values_spec (vs0 : Slice (alloc.vec.Vec value.Value))
    (hmax : (vs0.val.map (·.val.length)).sum ≤ Usize.max) :
    packets.take_bulk_param_values vs0 ⦃ r =>
      r.1.val.map bulkIV = vs0.val.flatMap (fun r => r.val.map ivOf) ⦄ := by
  unfold packets.take_bulk_param_values
  exact take_values_loop_spec vs0 hmax 0#usize vs0 _ (by simp) rfl rfl (by simp) (by simp)

private def FT (ts : List (Nat × Nat)) (row : alloc.vec.Vec value.Value) : List (Nat × Nat) :=
  List.zipWith bulkMerge ts (row.val.map (fun v => bulkTy (Val.ofValue v)))

private theorem new_loop_spec (stmt_id : U32) (bf : constants.StmtBulkExecuteFlags)
    (values : alloc.vec.Vec (alloc.vec.Vec value.Value)) (arity : Usize)
    (hv : (values.val.map (·.val.length)).sum ≤ Usize.max) (T0 : List (Nat × Nat))
    (it : core.ops.range.Range Usize) (tys : alloc.vec.Vec packets.StmtBulkExecuteParamType)
    (he : it.end = alloc.vec.Vec.len values) (hs : it.start.val ≤ values.val.length)
    (hpre : ∀ row ∈ values.val.take it.start.val, row.val.length = arity.val)
    (htys : tys.val.map SBParam.ptOf = (values.val.take it.start.val).foldl FT T0)
    (htl : tys.val.length ≤ arity.val) :
    packets.ComStmtBulkExecuteRequest.new_loop it stmt_id bf values arity tys ⦃ r =>
      (values.val.all (fun row => row.val.length == arity.val) = true → ∃ x, r = .Ok x ∧
        BulkReq.of x = ⟨stmt_id.val, bf.val, values.val.foldl FT T0,
          values.val.flatMap (fun row => row.val.map ivOf)⟩) ∧
      (values.val.all (fun row => row.val.length == arity.val) = false → r = .Err .MixedArity) ⦄ := by
  unfold packets.ComStmtBulkExecuteRequest.new_loop
  apply loop.spec_decr_nat (fun p => values.val.length - p.1.start.val)
    (fun p => p.1.end = alloc.vec.Vec.len values ∧ p.1.start.val ≤ values.val.length ∧
      (∀ row ∈ values.val.take p.1.start.val, row.val.length = arity.val) ∧
      p.2.val.map SBParam.ptOf = (values.val.take p.1.start.val).foldl FT T0 ∧
      p.2.val.length ≤ arity.val)
  · rintro ⟨it, ts⟩ ⟨h1, h2, h3, h4, h5⟩
    have h1' : it.end = alloc.vec.Vec.len values := h1
    have hen : it.end.val = values.val.length := by rw [h1']; simp [alloc.vec.Vec.len]
    have h2' : it.start.val ≤ values.val.length := h2
    have h3' : ∀ row ∈ values.val.take it.start.val, row.val.length = arity.val := h3
    have h4' : ts.val.map SBParam.ptOf = (values.val.take it.start.val).foldl FT T0 := h4
    have h5' : ts.val.length ≤ arity.val := h5
    clear h1 h2 h3 h4 h5
    unfold packets.ComStmtBulkExecuteRequest.new_loop.body
    step as ⟨oo, iter1, o_post, o_post1⟩
    by_cases hc : it.start.val < it.end.val
    · simp only [hc, ite_true] at o_post
      obtain ⟨rfl, hi1⟩ := o_post
      simp only
      have hk : it.start.val < values.val.length := by omega
      step as ⟨v, hv'⟩
      split
      · rename_i hne
        simp only [WP.spec_ok]
        refine ⟨fun hall => ?_, fun _ => by simp⟩
        exfalso
        have hmem : v ∈ values.val := by rw [hv']; exact List.getElem_mem _
        have := List.all_eq_true.mp hall v hmem
        simp only [beq_iff_eq] at this
        simp only [bne_iff_ne, ne_eq] at hne
        apply hne
        apply UScalar.eq_of_val_eq
        simpa [alloc.vec.Vec.len] using this
      · rename_i hne
        have hva : v.val.length = arity.val := by
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
          have := congrArg UScalar.val hne
          simpa [alloc.vec.Vec.len] using this
        step with ptypes_spec (alloc.vec.Vec.deref v) as ⟨rt, hrt⟩
        have hlift : lift (alloc.vec.Vec.deref_mut ts) ⦃ a b =>
            a = ts.slice ∧ b = (fun s => ({ slice := s } : alloc.vec.Vec _)) ⦄ := (WP.spec_ok _).mpr ⟨rfl, rfl⟩
        step with hlift as ⟨sl, back, hsl, hb⟩
        subst hsl hb
        have hrtl : rt.val.length = arity.val := by
          have := congrArg List.length hrt
          simp only [List.length_map] at this
          rw [this]; simpa [alloc.vec.Vec.deref] using hva
        step with merge_spec ts.slice (alloc.vec.Vec.deref rt)
          (by
            have : ts.slice.val.length ≤ arity.val := h5'
            simp only [Slice.length]; simp [alloc.vec.Vec.deref]; omega) as ⟨s3, hs3⟩
        have hsucc : values.val.take (it.start.val + 1) = values.val.take it.start.val ++ [v] := by
          rw [take_succ_set' _ _ hk, hv']
        refine ⟨by rw [o_post1, h1'], by omega, ?_, ?_, ?_, by omega⟩
        · rw [hi1, hsucc]
          intro row hrow
          simp only [List.mem_append, List.mem_singleton] at hrow
          rcases hrow with hrow | rfl
          · exact h3' row hrow
          · exact hva
        · rw [hi1, hsucc, List.foldl_append, ← h4']
          simp only [List.foldl_cons, List.foldl_nil, FT]
          rw [show ({ slice := s3 } : alloc.vec.Vec _).val = s3.val from rfl, hs3]
          congr 1
          simpa [alloc.vec.Vec.deref] using hrt
        · have := congrArg List.length hs3
          simp only [List.length_map, List.length_zipWith] at this
          show s3.val.length ≤ arity.val
          rw [this]
          have : ts.slice.val.length ≤ arity.val := h5'
          omega
    · simp only [hc, ite_false] at o_post
      obtain ⟨rfl, -⟩ := o_post
      have heq : it.start.val = values.val.length := by omega
      rw [heq, List.take_length] at h3' h4'
      have hall : values.val.all (fun row => row.val.length == arity.val) = true := by
        apply List.all_eq_true.mpr
        intro row hrow
        simpa using h3' row hrow
      have hlift : lift (alloc.vec.Vec.deref_mut values) ⦃ a b =>
          a = values.slice ∧ b = (fun s => ({ slice := s } : alloc.vec.Vec _)) ⦄ := (WP.spec_ok _).mpr ⟨rfl, rfl⟩
      step with hlift as ⟨sl, back, hsl, hb⟩
      subst hsl hb
      step with take_values_spec values.slice hv as ⟨vals, rest, hvals⟩
      have hcu : misc.raw.int.ConstU8.new packets.InvalidComStmtBulkExecuteHeader 250#u8 ⦃ _ => True ⦄ := by
        rw [misc.raw.int.ConstU8.new_eq]; exact (WP.spec_ok _).mpr trivial
      step with hcu
      have hri : misc.raw.int.RawInt.new misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 stmt_id
          ⦃ r => r.1 = stmt_id ⦄ := by
        rw [misc.raw.int.RawInt.new_eq]; exact (WP.spec_ok _).mpr rfl
      step with hri as ⟨ri, hri'⟩
      have hcc : misc.raw._const.Const.new misc.raw.int.LeU16 bf ⦃ c => c.1 = bf ⦄ := by
        rw [misc.raw._const.Const.new_eq]; exact (WP.spec_ok _).mpr rfl
      step with hcc as ⟨cc, hcc'⟩
      have hseq : misc.raw.seq.Seq.new misc.raw.seq.Unknown packets.StmtBulkExecuteParamType.Insts.CoreCloneClone
          (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
            packets.StmtBulkExecuteParamType.Insts.CoreCloneClone)) ts ⦃ x => cowList x.1 = ts.val ⦄ := by
        rw [misc.raw.seq.Seq.new_eq _ _ _ _ (.Owned ts) (by rfl)]
        exact (WP.spec_ok _).mpr rfl
      step with hseq as ⟨sq, hsq⟩
      refine ⟨fun _ => ⟨_, rfl, ?_⟩, fun h => by simp [hall] at h⟩
      simp only [BulkReq.of, hri', hcc', hsq, BulkReq.mk.injEq, true_and]
      refine ⟨?_, ?_⟩
      · rw [← h4']; rfl
      · exact hvals
  · exact ⟨he, hs, hpre, htys, htl⟩

private theorem foldl_FT_nil (l : List (alloc.vec.Vec value.Value)) : l.foldl FT [] = [] := by
  induction l with
  | nil => rfl
  | cons r l ih => simpa [FT] using ih

private theorem foldl_FT_eq (l : List (alloc.vec.Vec value.Value)) (T0 : List (Nat × Nat)) :
    l.foldl FT T0 = (l.map (fun row => row.val.map Val.ofValue)).foldl
      (fun ts row => List.zipWith bulkMerge ts (row.map bulkTy)) T0 := by
  rw [List.foldl_map]
  congr 1
  funext ts row
  simp [FT, List.map_map, Function.comp_def]

/-- `ComStmtBulkExecuteRequest::new(stmt_id, bulk_flags, rows)`: exactly `bulkNewOut` (`NoParams`
    for no rows, `MixedArity` if the rows differ in length, else the statement id, the flags,
    the merged types `bulkTypes` if the flags have `SEND_TYPES_TO_SERVER`, and every value with
    its indicator). Precondition: the number of values fits in a `usize`. -/
theorem packets.ComStmtBulkExecuteRequest.new_spec (stmt_id : U32)
    (bulk_flags : constants.StmtBulkExecuteFlags) (values : alloc.vec.Vec (alloc.vec.Vec value.Value))
    (hv : (values.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.new stmt_id bulk_flags values ⦃ r =>
      (bulkNewOut stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue))).Matches r ⦄ := by
  unfold packets.ComStmtBulkExecuteRequest.new
  step as ⟨b, hb⟩
  split
  · rename_i hbt
    have hnil : values.val = [] := by
      rw [hbt] at hb
      simpa [alloc.vec.Vec.length] using hb.symm
    simp [bulkNewOut, hnil, BulkNewOut.Matches]
  · rename_i hbt
    obtain ⟨r0, rs, hrs⟩ : ∃ r0 rs, values.val = r0 :: rs := by
      cases h : values.val with
      | nil => exfalso; apply hbt; rw [hb]; simp [alloc.vec.Vec.length, h]
      | cons r0 rs => exact ⟨r0, rs, rfl⟩
    step as ⟨v, hv0⟩
    have hvr : v = r0 := by rw [hv0]; simp [hrs]
    subst hvr
    simp only [contains_types, bind_ok]
    have hv' : (values.val.map (·.val.length)).sum ≤ Usize.max := by simpa using hv
    have key : ∀ (T0 : List (Nat × Nat)) (tys : alloc.vec.Vec packets.StmtBulkExecuteParamType),
        tys.val.map SBParam.ptOf = T0 → tys.val.length ≤ (alloc.vec.Vec.len v).val →
        (values.val.foldl FT T0 = if hasFlag bulk_flags.val SEND_TYPES_TO_SERVER then
            bulkTypes (values.val.map (fun row => row.val.map Val.ofValue)) else []) →
        packets.ComStmtBulkExecuteRequest.new_loop { start := 0#usize, «end» := alloc.vec.Vec.len values }
          stmt_id bulk_flags values (alloc.vec.Vec.len v) tys ⦃ r =>
          (bulkNewOut stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue))).Matches r ⦄ := by
      intro T0 tys htys htl hT
      apply WP.spec_mono (new_loop_spec stmt_id bulk_flags values (alloc.vec.Vec.len v) hv' T0 _ tys rfl
        (by simp) (by simp) (by simpa using htys) htl)
      rintro r ⟨hA, hB⟩
      have hall_eq : (values.val.map (fun row => row.val.map Val.ofValue)).all
          (fun r => r.length == (v.val.map Val.ofValue).length) =
          values.val.all (fun row => row.val.length == (alloc.vec.Vec.len v).val) := by
        simp [List.all_map, Function.comp_def, alloc.vec.Vec.len]
      have hmatch : bulkNewOut stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue)) =
          if (values.val.map (fun row => row.val.map Val.ofValue)).all
              (fun r => r.length == (v.val.map Val.ofValue).length) then
            .ok (bulkNew stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue)))
          else .mixedArity := by
        rw [hrs]; rfl
      rw [hmatch, hall_eq]
      cases hall : values.val.all (fun row => row.val.length == (alloc.vec.Vec.len v).val)
      · simp only [Bool.false_eq_true, ite_false, BulkNewOut.Matches]
        exact hB hall
      · simp only [ite_true, BulkNewOut.Matches]
        obtain ⟨x, hx, hxq⟩ := hA hall
        refine ⟨x, hx, ?_⟩
        rw [hxq, hT]
        simp only [bulkNew, BulkReq.mk.injEq, true_and]
        simp [List.flatMap, List.map_flatten, Function.comp_def]
    split
    · rename_i hft
      step with ptypes_spec (alloc.vec.Vec.deref v) as ⟨tys, htys⟩
      apply key _ tys htys
      · have := congrArg List.length htys
        simp only [List.length_map] at this
        simp [this, alloc.vec.Vec.deref, alloc.vec.Vec.len]
      · rw [hft, ite_eq_left rfl, foldl_FT_eq, hrs]
        simp [bulkTypes, alloc.vec.Vec.deref, List.map_map, Function.comp_def]
    · rename_i hft
      simp only [bind_ok]
      apply key [] (alloc.vec.Vec.new packets.StmtBulkExecuteParamType) (by simp) (by simp)
      rw [foldl_FT_nil]
      simp [hft]

end mysql_common
