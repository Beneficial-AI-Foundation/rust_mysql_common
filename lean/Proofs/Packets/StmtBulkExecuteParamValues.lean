import Defs
import Proofs.Util.StmtBulkParam
import Proofs.Packets.StmtBulkExecuteParamValue

/-! Statements for `struct StmtBulkExecuteParamValues and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Helper lemmas:
`Proofs/Util/StmtBulkParam.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `AsRef<[StmtBulkExecuteParamValue]>`: the values. -/
theorem packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref_spec
    (self : packets.StmtBulkExecuteParamValues) :
    packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref self ⦃ s =>
      s.val = self.values.val ⦄ := by
  simp [packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref,
    alloc.vec.Vec.deref]

/-- `MyDeserialize for StmtBulkExecuteParamValues`: `SIZE` is `None`. -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none := by
  unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE; rfl

private theorem de_loop_unfold (it : core.ops.range.Range Usize)
    (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags)) (buf : io.ParseBuf)
    (values : alloc.vec.Vec packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop
      it params buf values =
      (do
        let r ← packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
          params it buf values
        match r with
        | .cont (a, b, c) =>
          packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop
            a params b c
        | .done x => ok x) := by
  conv_lhs =>
    unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop
    rw [loop]
  congr 1
  funext r
  rcases r with ⟨a, b, c⟩ | x <;> rfl

private theorem de_loop_spec (h64 : Target64)
    (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (ps : List (constants.ColumnType × constants.ColumnFlags)) (it : core.ops.range.Range Usize)
    (buf : io.ParseBuf) (values : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hend : it.end.val = params.length) (hps : ps = params.val.drop it.start.val)
    (hcap : values.length + ps.length ≤ Usize.max)
    (r0 : Option (List (Nat × Val))) (rest0 : List U8)
    (h : bulkValuesRead (ps.map (fun p => (p.1, isUnsigned p.2))) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop
      it params buf values ⦃ r rest =>
      (okPart r).map (fun vs => vs.values.val.map bulkIV) = r0.map (fun l => values.val.map bulkIV ++ l) ∧
      rest.val = rest0 ⦄ := by
  induction ps generalizing it buf values r0 rest0 with
  | nil =>
    rw [de_loop_unfold]
    unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
    have hge : params.length ≤ it.start.val := by
      have := congrArg List.length hps
      simp at this; simp [alloc.vec.Vec.length]; omega
    simp only [List.map_nil, bulkValuesRead, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show ¬ (it.start.val < it.end.val) by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp [okPart]
  | cons q ps ih =>
    rw [de_loop_unfold]
    unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
    have hlt : it.start.val < params.length := by
      have := congrArg List.length hps
      simp at this; simp [alloc.vec.Vec.length]; omega
    have hlt' : it.start.val < params.val.length := by simpa [alloc.vec.Vec.length] using hlt
    rw [List.drop_eq_getElem_cons hlt'] at hps
    obtain ⟨hq, hps'⟩ := List.cons.inj hps
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show it.start.val < it.end.val by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    step*
    rw [x_post, ← hq]
    obtain ⟨ct, fl⟩ := q
    simp only [List.map_cons, bulkValuesRead] at h
    cases hv : bulkValueRead ct (isUnsigned fl) buf.val with
    | panic e => rw [hv] at h; simp at h
    | unknown => rw [hv] at h; simp at h
    | done rv rest1 =>
      rw [hv] at h
      apply WP.spec_bind (packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec
        h64 ct fl buf rv rest1 hv)
      rintro ⟨r, buf1⟩ ⟨hr1, hr2⟩
      cases rv with
      | none =>
        simp only [ReadOut.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases r with
        | Ok w => simp [okPart] at hr1
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, hr2]
      | some v =>
        cases r with
        | Err e => simp [okPart] at hr1
        | Ok w =>
          simp only [okPart, Option.map_some, Option.some.injEq] at hr1
          simp only at h
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          simp only [List.length_cons] at hcap
          apply WP.spec_bind (alloc.vec.Vec.push_spec values w (by simp [alloc.vec.Vec.length] at hcap; scalar_tac))
          intro values1 hval
          have hl1 : values1.length = values.length + 1 := by
            simp [alloc.vec.Vec.length, hval]
          cases hrest : bulkValuesRead (List.map (fun p => (p.1, isUnsigned p.2)) ps) rest1 with
          | panic e => rw [hrest] at h; simp at h
          | unknown => rw [hrest] at h; simp at h
          | done rvs rest2 =>
            rw [hrest] at h
            have := ih it1 buf1 values1 (by rw [he]; exact hend) (by rw [ho2]; exact hps') (by omega)
              rvs rest2 (by rw [hr2]; exact hrest)
            apply WP.spec_mono this
            rintro ⟨r', rest'⟩ ⟨h1, h2⟩
            cases rvs with
            | none =>
              simp only [ReadOut.done.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp_all
            | some vs =>
              simp only [ReadOut.done.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp_all

private theorem de_loop_panic (h64 : Target64)
    (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (ps : List (constants.ColumnType × constants.ColumnFlags)) (it : core.ops.range.Range Usize)
    (buf : io.ParseBuf) (values : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (hend : it.end.val = params.length) (hps : ps = params.val.drop it.start.val)
    (hcap : values.length + ps.length ≤ Usize.max) (e : Error)
    (h : bulkValuesRead (ps.map (fun p => (p.1, isUnsigned p.2))) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop
      it params buf values = fail e := by
  induction ps generalizing it buf values with
  | nil => simp [bulkValuesRead] at h
  | cons q ps ih =>
    rw [de_loop_unfold]
    have hlt : it.start.val < params.length := by
      have := congrArg List.length hps
      simp at this; simp [alloc.vec.Vec.length]; omega
    have hlt' : it.start.val < params.val.length := by simpa [alloc.vec.Vec.length] using hlt
    rw [List.drop_eq_getElem_cons hlt'] at hps
    obtain ⟨hq, hps'⟩ := List.cons.inj hps
    obtain ⟨ct, fl⟩ := q
    simp only [List.map_cons, bulkValuesRead] at h
    simp only [List.length_cons] at hcap
    cases hv : bulkValueRead ct (isUnsigned fl) buf.val with
    | unknown => rw [hv] at h; simp at h
    | panic e' =>
      rw [hv] at h
      simp only [ReadOut.panic.injEq] at h
      subst h
      apply PBUtil.bind_fail_left
      unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
      apply PBUtil.bind_fail_of_spec (core.iter.range.IteratorRange.next_Usize_some_spec it (by omega))
      rintro ⟨o, it1⟩ ⟨rfl, -, -⟩
      simp only [alloc.vec.Vec.index_slice_index]
      apply PBUtil.bind_fail_of_spec (alloc.vec.Vec.index_usize_spec params it.start hlt)
      intro x hx
      rw [hx, ← hq,
        packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_panics
          h64 ct fl buf e' hv]
      exact Std.bind_tc_fail _ _
    | done rv rest1 =>
      rw [hv] at h
      cases rv with
      | none => cases h
      | some v =>
        simp only at h
        cases hrest : bulkValuesRead (List.map (fun p => (p.1, isUnsigned p.2)) ps) rest1 with
        | done rr _ => rw [hrest] at h; cases rr <;> cases h
        | unknown => rw [hrest] at h; simp at h
        | panic e2 =>
          rw [hrest] at h
          simp only [ReadOut.panic.injEq] at h
          subst h
          have hbody : packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
              params it buf values ⦃ r => ∃ it1 buf1 values1, r = .cont (it1, buf1, values1) ∧
                it1.end = it.end ∧ it1.start.val = it.start.val + 1 ∧ buf1.val = rest1 ∧
                values1.length = values.length + 1 ⦄ := by
            unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_loop.body
            apply WP.spec_bind (core.iter.range.IteratorRange.next_Usize_some_spec it (by omega))
            rintro ⟨o, it1⟩ ⟨rfl, ho2, he⟩
            simp only [alloc.vec.Vec.index_slice_index]
            apply WP.spec_bind (alloc.vec.Vec.index_usize_spec params it.start hlt)
            intro x hx
            rw [hx, ← hq]
            apply WP.spec_bind (packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec
              h64 ct fl buf _ _ hv)
            rintro ⟨r, buf1⟩ ⟨hr1, hr2⟩
            cases r with
            | Err _ => simp [okPart] at hr1
            | Ok w =>
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              apply WP.spec_bind (alloc.vec.Vec.push_spec values w (by simp [alloc.vec.Vec.length] at hcap; scalar_tac))
              intro values1 hval
              refine (WP.spec_ok _).mpr ⟨it1, buf1, values1, rfl, he, ho2, hr2, ?_⟩
              simp [hval]
          apply PBUtil.bind_fail_of_spec hbody
          rintro r ⟨it1, buf1, values1, rfl, he, ho2, hb1, hl1⟩
          exact ih it1 buf1 values1 (by rw [he]; exact hend) (by rw [ho2]; exact hps') (by omega)
            (by rw [hb1]; exact hrest)

/-- `MyDeserialize for StmtBulkExecuteParamValues` with the parameters `params`: one value per
    parameter (`bulkValuesRead`), exactly, whenever that reader returns. -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (r0 : Option (List (Nat × Val))) (rest0 : List U8)
    (h : bulkValuesRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map (fun vs => vs.values.val.map bulkIV) = r0 ∧ rest.val = rest0 ⦄ := by
  unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize
  have hl : params.length ≤ Usize.max := by scalar_tac
  have := de_loop_spec h64 params params.val { start := 0#usize, «end» := alloc.vec.Vec.len params } buf
    (alloc.vec.Vec.with_capacity packets.StmtBulkExecuteParamValue (alloc.vec.Vec.len params))
    (by simp) (by simp) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length] at hl ⊢) r0 rest0
    (by simpa [bulkParams] using h)
  apply WP.spec_bind this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  refine (WP.spec_ok _).mpr ⟨?_, h2⟩
  rw [h1]
  cases r0 <;> simp [alloc.vec.Vec.with_capacity]

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValues` panics where `bulkValuesRead`
    does: a non-`NULL` indicator for a parameter whose column type the binary reader does not
    support (`TIMESTAMP2`, `DATETIME2`, `TIME2`, `TYPED_ARRAY`, `UNKNOWN`). -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (e : Error) (h : bulkValuesRead (bulkParams params) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e := by
  unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize
  have hl : params.length ≤ Usize.max := by scalar_tac
  dsimp only
  rw [de_loop_panic h64 params params.val { start := 0#usize, «end» := alloc.vec.Vec.len params } buf
    (alloc.vec.Vec.with_capacity packets.StmtBulkExecuteParamValue (alloc.vec.Vec.len params))
    (by simp) (by simp) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length] at hl ⊢) e
    (by simpa [bulkParams] using h)]
  exact Std.bind_tc_fail _ _

private theorem ser_loop_unfold (it : core.ops.range.Range Usize)
    (v : alloc.vec.Vec packets.StmtBulkExecuteParamValue) (buf : alloc.vec.Vec U8) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop it v buf =
      (do
        let r ← packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop.body v it buf
        match r with
        | .cont (a, b) => packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop a v b
        | .done x => ok x) := by
  conv_lhs => unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop; rw [loop]
  congr 1
  funext r
  rcases r with ⟨a, b⟩ | x <;> rfl

private theorem ser_loop_spec (v : alloc.vec.Vec packets.StmtBulkExecuteParamValue)
    (xs : List packets.StmtBulkExecuteParamValue) (it : core.ops.range.Range Usize) (buf : alloc.vec.Vec U8)
    (hend : it.end.val = v.length) (hxs : xs = v.val.drop it.start.val)
    (h : buf.length + ((xs.map bulkIV).flatMap bulkValueEnc).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop it v buf ⦃ b =>
      b.val = buf.val ++ (xs.map bulkIV).flatMap bulkValueEnc ⦄ := by
  induction xs generalizing it buf with
  | nil =>
    rw [ser_loop_unfold]
    unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop.body
    have hge : v.length ≤ it.start.val := by
      have := congrArg List.length hxs
      simp at this; simp [alloc.vec.Vec.length]; omega
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show ¬ (it.start.val < it.end.val) by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp
  | cons y xs ih =>
    rw [ser_loop_unfold]
    unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_loop.body
    have hlt : it.start.val < v.length := by
      have := congrArg List.length hxs
      simp at this; simp [alloc.vec.Vec.length]; omega
    have hlt' : it.start.val < v.val.length := by simpa [alloc.vec.Vec.length] using hlt
    rw [List.drop_eq_getElem_cons hlt'] at hxs
    obtain ⟨hx, hxs'⟩ := List.cons.inj hxs
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show it.start.val < it.end.val by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    step*
    rw [x_post, ← hx]
    simp only [List.map_cons, List.flatMap_cons, List.length_append] at h ⊢
    apply WP.spec_bind (packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize_spec
      y buf (by omega))
    intro b1 hb1
    have hl : b1.length = buf.length + (bulkValueEnc (bulkIV y)).length := by
      simp only [alloc.vec.Vec.length, hb1, List.length_append]
    apply WP.spec_mono (ih it1 b1 (by rw [he]; exact hend) (by rw [ho2]; exact hxs') (by omega))
    intro b2 hb2
    rw [hb2, hb1]
    simp

/-- `MySerialize for StmtBulkExecuteParamValues`: appends each value (`bulkValueEnc`). -/
theorem packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValues) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((self.values.val.map bulkIV).flatMap bulkValueEnc).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (self.values.val.map bulkIV).flatMap bulkValueEnc ⦄ := by
  unfold packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize
  exact ser_loop_spec self.values self.values.val _ buf (by simp) (by simp) h

end mysql_common
