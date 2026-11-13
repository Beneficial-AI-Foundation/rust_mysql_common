import Defs

/-! Statements for `struct ComStmtBulkExecuteRequestBuilder and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

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
  sorry

/-- **Crate bug (crash path).** `new` panics (in debug builds; it wraps in release builds) for
    `max_allowed_packet < 4`: `max_allowed_packet - 4` underflows. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.new_underflow (stmt_id : U32) (max_allowed_packet : Usize)
    (h : max_allowed_packet.val < 4) :
    packets.ComStmtBulkExecuteRequestBuilder.new stmt_id max_allowed_packet = fail .integerOverflow := by
  sorry

/-- `with_named_params`: sets the named parameters; nothing else changes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.with_named_params_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) (named_params : Option (Slice (alloc.vec.Vec U8))) :
    packets.ComStmtBulkExecuteRequestBuilder.with_named_params self named_params ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with namedParams := named_params } ⦄ := by
  sorry

/-- `with_results`: requests unit results (`SEND_UNIT_RESULTS`); nothing else changes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.impl.with_results_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.impl.with_results self ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with withResults := true } ⦄ := by
  sorry

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
  sorry

/-- `add_row` keeps the builder's bookkeeping right (`BulkBuilder.Inv`): in particular, while it
    has rows, the request `build` makes fits in `max_allowed_packet - 4` (`build_fits`). -/
theorem packets.ComStmtBulkExecuteRequestBuilder.add_row_inv
    (self : packets.ComStmtBulkExecuteRequestBuilder) (params : alloc.vec.Vec value.Value)
    (hinv : (BulkBuilder.of self).Inv)
    (hov : 7 + 2 * params.length + self.payload_len.val + bulkRowLen (params.val.map Val.ofValue)
      ≤ Usize.max)
    (hlen : self.params_set.length < Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row self params ⦃ _ b => (BulkBuilder.of b).Inv ⦄ := by
  sorry

/-- `has_rows`: whether a row has been added since the last `build`. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.has_rows_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.has_rows self ⦃ b => b = decide (self.params_set.val ≠ []) ⦄ := by
  sorry

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
  sorry

/-- Headline: a builder whose bookkeeping is right (every builder made by `new`, `add_row` and
    `build`) builds requests whose packet fits in `max_allowed_packet - 4` bytes. -/
theorem packets.ComStmtBulkExecuteRequestBuilder.build_fits
    (self : packets.ComStmtBulkExecuteRequestBuilder) (hinv : (BulkBuilder.of self).Inv)
    (hv : (self.params_set.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.build self ⦃ r b =>
      (∀ q, r = .Ok q → (bulkReqEnc (BulkReq.of q)).length ≤ self.max_payload_len.val) ∧
      (BulkBuilder.of b).Inv ⦄ := by
  sorry

end mysql_common
