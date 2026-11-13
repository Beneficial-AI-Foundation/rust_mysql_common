import Defs
import Proofs.Value.Value
import Proofs.Packets.ComStmtBulkExecuteRequest
import Proofs.Defs.LemmasStmtSession

/-! Statements for `struct ComStmtBulkExecuteRequestBuilder and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComStmtBulkExecuteRequestBuilder::new(stmt_id, max_allowed_packet)`, for
    `max_allowed_packet ≥ 4`: no rows, types still to be sent, no unit results, no arity, no
    named parameters, a maximum payload of `max_allowed_packet - 4`. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.new_spec (stmt_id : U32) (max_allowed_packet : Usize)
    (h : 4 ≤ max_allowed_packet.val) :
    packets.ComStmtBulkExecuteRequestBuilder.new stmt_id max_allowed_packet ⦃ b =>
      BulkBuilder.of b = ⟨stmt_id.val, true, false, [], 0, none, none, max_allowed_packet.val - 4⟩ ∧
      (BulkBuilder.of b).Inv ⦄ := by
  unfold packets.ComStmtBulkExecuteRequestBuilder.new
  step*
  refine ⟨?_, ?_⟩
  · simp [BulkBuilder.of, i_post]
  · simp [BulkBuilder.of, BulkBuilder.Inv]

/-- **Crate bug (crash path).** `new` panics (in debug builds; it wraps in release builds) for
    `max_allowed_packet < 4`: `max_allowed_packet - 4` underflows. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.new_underflow (stmt_id : U32) (max_allowed_packet : Usize)
    (h : max_allowed_packet.val < 4) :
    packets.ComStmtBulkExecuteRequestBuilder.new stmt_id max_allowed_packet = fail .integerOverflow := by
  unfold packets.ComStmtBulkExecuteRequestBuilder.new
  have : max_allowed_packet - 4#usize = fail .integerOverflow := by
    have h4 : max_allowed_packet.val < (4#usize).val := by simpa using h
    simp only [HSub.hSub, Sub.sub, UScalar.sub, h4, ite_true]
  simp [this]

/-- `with_named_params`: sets the named parameters; nothing else changes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.with_named_params_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) (named_params : Option (Slice (alloc.vec.Vec U8))) :
    packets.ComStmtBulkExecuteRequestBuilder.with_named_params self named_params ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with namedParams := named_params } ⦄ := by
  simp [packets.ComStmtBulkExecuteRequestBuilder.with_named_params, BulkBuilder.of]

/-- `with_results`: requests unit results (`SEND_UNIT_RESULTS`); nothing else changes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.impl.with_results_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.impl.with_results self ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with withResults := true } ⦄ := by
  simp [packets.ComStmtBulkExecuteRequestBuilder.impl.with_results, BulkBuilder.of]

private abbrev lensOf (l : List value.Value) : List Nat := l.map (fun v => 1 + (binEnc (Val.ofValue v)).length)

private theorem usize_max_lt : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]

private theorem sum_take_le (l : List Nat) (k : Nat) : (l.take k).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop k l)
  rw [List.sum_append] at this; omega

private theorem sum_take_succ (l : List Nat) (k : Nat) (hk : k < l.length) :
    (l.take (k + 1)).sum = (l.take k).sum + l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.sum_append]; simp

private theorem add_row_loop_spec (params : alloc.vec.Vec value.Value) (k : Usize) (dl : Usize)
    (hk : k.val ≤ params.length)
    (hdl : dl.val = ((lensOf params.val).take k.val).sum)
    (hmax : (lensOf params.val).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row_loop { start := k, «end» := alloc.vec.Vec.len params } params dl
      ⦃ dl' => dl'.val = (lensOf params.val).sum ⦄ := by
  unfold packets.ComStmtBulkExecuteRequestBuilder.add_row_loop
  apply loop.spec_decr_nat (fun p => params.length - p.1.start.val)
    (fun p => p.1.end = alloc.vec.Vec.len params ∧ p.1.start.val ≤ params.length ∧
      p.2.val = ((lensOf params.val).take p.1.start.val).sum)
  · rintro ⟨it, d⟩ ⟨h1, h2, h5⟩
    have h1' : it.end = alloc.vec.Vec.len params := h1
    have hend : it.end.val = params.length := by rw [h1']; simp
    unfold packets.ComStmtBulkExecuteRequestBuilder.add_row_loop.body
    step*
    · have hc : ¬ it.start.val < it.end.val := by
        intro hc; simp only [hc, ite_true] at o_post; simp_all
      have heq : it.start.val = params.val.length := by simp only [alloc.vec.Vec.length] at hend h2; omega
      have h5' := h5
      simp only [heq] at h5'
      rw [List.take_of_length_le (by simp)] at h5'
      exact h5'
    · split_ifs at o_post with hc
      · simp_all
      · simp_all
    · have hc : it.start.val < it.end.val := by
        by_contra hc; simp only [hc, ite_false] at o_post; simp_all
      have hi1 : iter1.start.val = it.start.val + 1 := by
        simp only [hc, ite_true] at o_post; exact o_post.2
      have hi : i = it.start := by
        have o_post' := o_post
        simp only [hc, ite_true] at o_post'
        obtain ⟨ho, -⟩ := o_post'
        subst ho; exact (Option.some.inj ‹_›).symm
      subst hi
      have hlen : it.start.val < params.val.length := by simp only [alloc.vec.Vec.length] at hend; omega
      have hlenL : it.start.val < (lensOf params.val).length := by simp [lensOf]; omega
      have hs1 := sum_take_succ (lensOf params.val) it.start.val hlenL
      have hs2 := sum_take_le (lensOf params.val) (it.start.val + 1)
      have hget : (lensOf params.val)[it.start.val]'hlenL = 1 + (binEnc (Val.ofValue v)).length := by
        simp [lensOf, v_post]
      have hmx := usize_max_lt
      step with value.Value.bin_len_spec v (by omega) as ⟨l, hl⟩
      have hxv : (UScalar.cast .Usize l).val = (binEnc (Val.ofValue v)).length := by
        rw [UScalar.cast_val_eq, hl]; apply Nat.mod_eq_of_lt
        have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
          simp only [Usize.max, Usize.numBits, UScalarTy.numBits]; have := Nat.one_le_two_pow (n := System.Platform.numBits); omega
        omega
      simp only [lift, Aeneas.Std.bind_ok]
      have hd5 : d.val = ((lensOf params.val).take it.start.val).sum := h5
      split
      · rename_i hz
        step as ⟨d1, hd1⟩
        refine ⟨by simp [o_post1, h1'], by simp only [alloc.vec.Vec.length]; omega, ?_,
          by simp only [alloc.vec.Vec.length]; omega⟩
        rw [hi1, hs1, hget, hd1, hd5]; omega
      · step as ⟨x1, hx1⟩
        step as ⟨d1, hd1⟩
        refine ⟨by simp [o_post1, h1'], by simp only [alloc.vec.Vec.length]; omega, ?_,
          by simp only [alloc.vec.Vec.length]; omega⟩
        rw [hi1, hs1, hget, hd1, hd5, hx1]; omega
  · exact ⟨rfl, hk, hdl⟩

/-- `add_row(row)`: exactly `bulkAddRow` (the arity is fixed by the first row offered; a row is
    added only while the request stays within `max_allowed_packet - 4`, otherwise handed back,
    or rejected with `RowTooLarge` if the builder has no rows). Preconditions: the size
    arithmetic does not overflow `usize`, and there is room for one more row (both true of any
    real builder). -/
theorem packets.ComStmtBulkExecuteRequestBuilder.add_row_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) (params : alloc.vec.Vec value.Value)
    (hov : 7 + 2 * params.length + self.payload_len.val + bulkRowLen (params.val.map Val.ofValue)
      ≤ Usize.max)
    (hlen : self.params_set.length < Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row self params ⦃ r b =>
      (bulkAddRow (BulkBuilder.of self) params.val).1.Matches params r ∧
      BulkBuilder.of b = (bulkAddRow (BulkBuilder.of self) params.val).2 ⦄ := by
  have hrl : bulkRowLen (params.val.map Val.ofValue) = (lensOf params.val).sum := by
    simp [bulkRowLen, lensOf, Function.comp_def]
  rw [hrl] at hov
  obtain ⟨sid, wt, wr, ps, pl, ar, np, mx⟩ := self
  unfold packets.ComStmtBulkExecuteRequestBuilder.add_row
  simp only [core.convert.IntoFrom.into,
    packets.BulkExecuteRequestBuilderError.Insts.CoreConvertFromBulkExecuteRequestError.from]
  simp only at hov hlen
  have hmx := usize_max_lt
  have hlp : (alloc.vec.Vec.len params).val = params.length := by simp
  have hloop := add_row_loop_spec params 0#usize 0#usize (by simp) (by simp) (by omega)
  have hlen' : ps.val.length < Usize.max := hlen
  have hpl : params.length ≤ Usize.max := by scalar_tac
  have hps0 : ps.val.map (·.val) = [] ↔ ps.length = 0 := by simp
  cases ar with
  | none =>
    simp only [bind_ok]
    by_cases hwt : wt <;> by_cases hp0 : pl = 0#usize <;> simp only [hwt, hp0, ite_true, ite_false] <;>
    step* <;>
    simp_all [BulkBuilder.of, bulkAddRow, AddRowOut.Matches] <;> split_ifs <;> simp_all <;> omega
  | some a =>
    simp only [bind_ok]
    by_cases hwt : wt <;> by_cases hp0 : pl = 0#usize <;> simp only [hwt, hp0, ite_true, ite_false] <;>
    step* <;>
    simp_all [BulkBuilder.of, bulkAddRow, AddRowOut.Matches] <;> split_ifs <;> simp_all <;> omega

/-- `add_row` keeps the builder's bookkeeping right (`BulkBuilder.Inv`): in particular, while it
    has rows, the request `build` makes fits in `max_allowed_packet - 4` (`build_fits`). -/
theorem packets.ComStmtBulkExecuteRequestBuilder.add_row_inv
    (self : packets.ComStmtBulkExecuteRequestBuilder) (params : alloc.vec.Vec value.Value)
    (hinv : (BulkBuilder.of self).Inv)
    (hov : 7 + 2 * params.length + self.payload_len.val + bulkRowLen (params.val.map Val.ofValue)
      ≤ Usize.max)
    (hlen : self.params_set.length < Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row self params ⦃ _ b => (BulkBuilder.of b).Inv ⦄ := by
  apply WP.spec_mono (packets.ComStmtBulkExecuteRequestBuilder.add_row_spec self params hov hlen)
  rintro ⟨_, b⟩ ⟨_, hb⟩
  show (BulkBuilder.of b).Inv
  rw [hb]
  exact bulkAddRow_inv _ _ hinv

/-- `has_rows`: whether a row has been added since the last `build`. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.has_rows_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.has_rows self ⦃ b => b = decide (self.params_set.val ≠ []) ⦄ := by
  simp [packets.ComStmtBulkExecuteRequestBuilder.has_rows, alloc.vec.Vec.is_empty]

/-- `build`: the request `ComStmtBulkExecuteRequest::new` makes of the rows added (`bulkNewOut`;
    `NoParams` without rows), with `SEND_UNIT_RESULTS` if `with_results` and
    `SEND_TYPES_TO_SERVER` only in the builder's first request (`BulkBuilder.flags`); the
    builder is left without rows, with the types no longer to be sent and the arity kept.
    **Crate behaviour to note**: later requests of the same builder do not send the parameter
    types, so the server reuses the first request's types, although the later rows' types
    (`bulkTypes`) may differ (e.g. a first batch of `NULL`s has type `MYSQL_TYPE_NULL`).
    Precondition: the number of values fits in a `usize`. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.build_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder)
    (hv : (self.params_set.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.build self ⦃ r b =>
      (bulkNewOut self.stmt_id.val (BulkBuilder.of self).flags
        (self.params_set.val.map (fun row => row.val.map Val.ofValue))).Matches r ∧
      BulkBuilder.of b = { BulkBuilder.of self with withTypes := false, payloadLen := 0, rows := [] } ⦄ := by
  obtain ⟨sid, wt, wr, ps, pl, ar, np, mx⟩ := self
  unfold packets.ComStmtBulkExecuteRequestBuilder.build
  simp only at hv ⊢
  cases wr <;> cases wt <;>
    simp only [constants.StmtBulkExecuteFlags.empty, constants.StmtBulkExecuteFlags.insert,
      constants.StmtBulkExecuteFlags.union, constants.StmtBulkExecuteFlags.SEND_UNIT_RESULTS,
      constants.StmtBulkExecuteFlags.SEND_TYPES_TO_SERVER, lift, bind_ok, ite_true, ite_false,
      Bool.false_eq_true, core.mem.replace] <;>
    (apply WP.spec_bind (packets.ComStmtBulkExecuteRequest.new_spec _ _ _ hv)
     intro r hr
     refine (WP.spec_ok _).mpr ⟨?_, ?_⟩
     · convert hr using 2
       simp [BulkBuilder.flags, BulkBuilder.of, SEND_UNIT_RESULTS, SEND_TYPES_TO_SERVER]
     · simp [BulkBuilder.of])

/-- Headline: a builder whose bookkeeping is right (every builder made by `new`, `add_row` and
    `build`) builds requests whose packet fits in `max_allowed_packet - 4` bytes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.build_fits
    (self : packets.ComStmtBulkExecuteRequestBuilder) (hinv : (BulkBuilder.of self).Inv)
    (hv : (self.params_set.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.build self ⦃ r b =>
      (∀ q, r = .Ok q → (bulkReqEnc (BulkReq.of q)).length ≤ self.max_payload_len.val) ∧
      (BulkBuilder.of b).Inv ⦄ := by
  apply WP.spec_mono (packets.ComStmtBulkExecuteRequestBuilder.build_spec self hv)
  rintro ⟨r, b⟩ ⟨hm, hb⟩
  refine ⟨?_, ?_⟩
  · intro q hq
    subst hq
    have hrows : (BulkBuilder.of self).rows.map (·.map Val.ofValue) =
        self.params_set.val.map (fun row => row.val.map Val.ofValue) := by
      simp [BulkBuilder.of]
    have := bulkBuild_fits (BulkBuilder.of self) hinv (BulkReq.of q) (by
      rw [hrows]
      have hsid : (BulkBuilder.of self).stmtId = self.stmt_id.val := rfl
      rw [hsid]
      revert hm
      cases bulkNewOut self.stmt_id.val (BulkBuilder.of self).flags
          (self.params_set.val.map (fun row => row.val.map Val.ofValue)) with
      | noParams => simp [BulkNewOut.Matches]
      | mixedArity => simp [BulkNewOut.Matches]
      | ok q0 =>
        rintro ⟨x, hx, hxq⟩
        cases hx; rw [hxq])
    exact this
  · rw [hb]
    simp [BulkBuilder.Inv]

end mysql_common
