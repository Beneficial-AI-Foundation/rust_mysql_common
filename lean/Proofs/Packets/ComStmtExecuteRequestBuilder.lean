import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Packets.NullBitmap
import Proofs.Packets.ComStmtExecuteRequest
import Proofs.Value.Value

/-! Statements for `struct ComStmtExecuteRequestBuilder and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

/-- `new`: the builder for the statement. -/
theorem packets.ComStmtExecuteRequestBuilder.new_eq (stmt_id : U32) :
    packets.ComStmtExecuteRequestBuilder.new stmt_id = ok { stmt_id } := by
  rfl

private abbrev nullsOf (l : List value.Value) : List Bool := l.map (fun v => isNullVal (Val.ofValue v))
private abbrev lensOf (l : List value.Value) : List Nat := l.map (fun v => (binEnc (Val.ofValue v)).length)

private theorem usize_max_lt : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]

private theorem sum_take_le (l : List Nat) (k : Nat) : (l.take k).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop k l)
  rw [List.sum_append] at this; omega

private theorem sum_take_succ (l : List Nat) (k : Nat) (hk : k < l.length) :
    (l.take (k + 1)).sum = (l.take k).sum + l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.sum_append]; simp

private theorem build_loop_spec (params : Slice value.Value) (k : Usize)
    (bm : packets.NullBitmap value.ClientSide (alloc.vec.Vec U8)) (dl : Usize)
    (hk : k.val ≤ params.length)
    (hbl : bm.1.length = nullBitmapLen 0 params.length)
    (hbits : ∀ pos, bitAt bm.1.val pos = ((nullsOf params.val).take k.val).getD pos false)
    (hdl : dl.val = ((lensOf params.val).take k.val).sum)
    (hmax : (lensOf params.val).sum ≤ Usize.max)
    (hn : params.length + 7 ≤ Usize.max) :
    packets.ComStmtExecuteRequestBuilder.build_loop { start := k, «end» := Slice.len params } params bm dl
      ⦃ bm' dl' => bm'.1.length = nullBitmapLen 0 params.length ∧
        (∀ pos, bitAt bm'.1.val pos = (nullsOf params.val).getD pos false) ∧
        dl'.val = (lensOf params.val).sum ⦄ := by
  unfold packets.ComStmtExecuteRequestBuilder.build_loop
  apply loop.spec_decr_nat (fun p => params.length - p.1.start.val)
    (fun p => p.1.end = Slice.len params ∧ p.1.start.val ≤ params.length ∧
      p.2.1.1.length = nullBitmapLen 0 params.length ∧
      (∀ pos, bitAt p.2.1.1.val pos = ((nullsOf params.val).take p.1.start.val).getD pos false) ∧
      p.2.2.val = ((lensOf params.val).take p.1.start.val).sum)
  · rintro ⟨it, b, d⟩ ⟨h1, h2, h3, h4, h5⟩
    have h1' : it.end = Slice.len params := h1
    have hend : it.end.val = params.length := by rw [h1']; simp [Slice.len]
    unfold packets.ComStmtExecuteRequestBuilder.build_loop.body
    step*
    · have hc : ¬ it.start.val < it.end.val := by
        intro hc; simp only [hc, ite_true] at o_post; simp_all
      have heq : it.start.val = params.val.length := by simp only [Slice.length] at hend h2; omega
      have h4' := h4; have h5' := h5; have h3' := h3
      simp only [heq] at h4' h5'
      rw [List.take_of_length_le (by simp)] at h4' h5'
      exact ⟨h3', h4', h5'⟩
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
      have hlen : it.start.val < params.val.length := by simp only [Slice.length] at hend; omega
      have hlenL : it.start.val < (lensOf params.val).length := by simp [lensOf]; omega
      have hs1 := sum_take_succ (lensOf params.val) it.start.val hlenL
      have hs2 := sum_take_le (lensOf params.val) (it.start.val + 1)
      have hget : (lensOf params.val)[it.start.val]'hlenL = (binEnc (Val.ofValue v)).length := by
        simp [lensOf, v_post]
      have hmx := usize_max_lt
      step with value.Value.bin_len_spec v (by omega) as ⟨l, hl⟩
      have hxv : (UScalar.cast .Usize l).val = (binEnc (Val.ofValue v)).length := by
        rw [UScalar.cast_val_eq, hl]; apply Nat.mod_eq_of_lt
        have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
          simp only [Usize.max, Usize.numBits, UScalarTy.numBits]; have := Nat.one_le_two_pow (n := System.Platform.numBits); omega
        omega
      simp only [lift, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_ok]
      have hb3 : b.1.length = nullBitmapLen 0 params.length := h3
      have hb4 : ∀ pos, bitAt b.1.val pos = ((nullsOf params.val).take it.start.val).getD pos false := h4
      have hd5 : d.val = ((lensOf params.val).take it.start.val).sum := h5
      have hlenN : it.start.val < (nullsOf params.val).length := by simp [nullsOf]; omega
      have hnget : (nullsOf params.val)[it.start.val]'hlenN = isNullVal (Val.ofValue v) := by
        simp [nullsOf, v_post]
      have hold : ((nullsOf params.val).take it.start.val).getD it.start.val false = false := by
        simp [List.getD_eq_getElem?_getD]
      split
      · rename_i hz
        have hnull : isNullVal (Val.ofValue v) = true :=
          (binEnc_eq_nil_iff _).mp (List.eq_nil_of_length_eq_zero (by omega))
        have hoffv := value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
        step with packets.NullBitmap.set_spec value.ClientSide.Insts.Mysql_commonValueSerializationSide
          value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET rfl b it.start true (by rw [hoffv]; scalar_tac)
          (by rw [hoffv, hb3]; simp only [nullBitmapLen]; omega) as ⟨bm1, hbm1a, hbm1b⟩
        refine ⟨by simp [o_post1, h1'], by simp only [Slice.length]; omega, by rw [hbm1a, hb3], ?_, ?_,
          by simp only [Slice.length]; omega⟩
        · intro pos
          change bitAt bm1.1.val pos = _
          rw [hbm1b pos, hoffv, Nat.add_zero, hi1, getD_take_succ _ _ _ _ hlenN]
          by_cases hp : pos = it.start.val
          · simp only [hp, ite_true, hnget, hnull]
          · simp only [hp, ite_false, hb4]
        · change d.val = _
          rw [hi1, hs1, hget, ← hd5]; omega
      · rename_i hz
        have hnn : isNullVal (Val.ofValue v) = false := by
          cases h : isNullVal (Val.ofValue v)
          · rfl
          · have := (binEnc_eq_nil_iff _).mpr h; rw [this] at hxv
            exact (hz (by simpa using hxv)).elim
        have hdx : d.val + (UScalar.cast .Usize l).val ≤ Usize.max := by rw [hd5, hxv]; omega
        step as ⟨d1, hd1⟩
        refine ⟨by simp [o_post1, h1'], by simp only [Slice.length]; omega, hb3, ?_, ?_,
          by simp only [Slice.length]; omega⟩
        · intro pos
          change bitAt b.1.val pos = _
          rw [hi1, getD_take_succ _ _ _ _ hlenN, hb4]
          by_cases hp : pos = it.start.val
          · simp only [hp, ite_true, hnget, hnn, hold]
          · simp only [hp, ite_false]
        · change d1.val = _
          rw [hi1, hs1, hget, hd1, hd5, hxv]
  · exact ⟨rfl, hk, hbl, hbits, hdl⟩

/-- `build(params)`: the request for the statement with no cursor, iteration count 1, the NULL bitmap of the parameters (offset 0; a parameter is NULL iff its binary encoding is empty), new-params-bound flag 1 and the parameters; `as_long_data` (also returned) iff the length the builder computes exceeds `MAX_PAYLOAD_LEN`. (The bound keeps that computation from overflowing.) -/
theorem packets.ComStmtExecuteRequestBuilder.build_spec (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value)
    (h : stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    packets.ComStmtExecuteRequestBuilder.build self params ⦃ req b =>
      req.stmt_id.1 = self.stmt_id ∧ req.flags.1.val = 0 ∧
      cowList req.bitmap.1 = nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v))) ∧
      req.params_flags.1.val = 1 ∧ req.params = params ∧ req.as_long_data = b ∧
      (b = true ↔ maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue)) ⦄ := by
  sorry

/-- Headline: `build` then `serialize` appends the protocol's `COM_STMT_EXECUTE` packet (`comStmtExecute`), with the `Bytes` values left out iff `as_long_data`, for at most 65536 parameters (beyond, the bitmap is truncated). -/
theorem packets.ComStmtExecuteRequestBuilder.build_serialize (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value) (buf : alloc.vec.Vec U8)
    (hn : params.length ≤ 65536) (h : buf.length + stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    (packets.ComStmtExecuteRequestBuilder.build self params >>= fun p =>
      packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize p.1 buf) ⦃ buf' =>
      buf'.val = buf.val ++ comStmtExecute self.stmt_id.val (params.val.map Val.ofValue)
        (decide (maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue))) ⦄ := by
  sorry

end mysql_common
