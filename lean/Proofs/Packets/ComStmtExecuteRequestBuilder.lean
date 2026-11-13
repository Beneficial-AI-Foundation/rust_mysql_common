import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Packets.NullBitmap
import Proofs.Packets.ComStmtExecuteRequest
import Proofs.Value.Value
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.ConstU32
import Proofs.Misc.Raw.Bytes.RawBytes

/-! Statements for `struct ComStmtExecuteRequestBuilder and its impls` (spec file: `Specs/Packets.lean`). Proofs: complete. -/

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

@[local step]
private theorem from_bytes_ok' {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8)) (bytes : U) :
    packets.NullBitmap.from_bytes inst asRef bytes ⦃ nb => nb.1 = bytes ⦄ := by
  rw [packets.NullBitmap.from_bytes_eq]; exact (WP.spec_ok _).mpr rfl

@[local step]
private theorem constu8_new_ok (T : Type) (N : U8) : misc.raw.int.ConstU8.new T N ⦃ _ => True ⦄ := by
  rw [misc.raw.int.ConstU8.new_eq]; exact (WP.spec_ok _).mpr trivial

@[local step]
private theorem constu32_new_ok (T : Type) (N : U32) : misc.raw.int.ConstU32.new T N ⦃ _ => True ⦄ := by
  rw [misc.raw.int.ConstU32.new_eq]; exact (WP.spec_ok _).mpr trivial

@[local step]
private theorem rawint_new_ok {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x ⦃ r => r.1 = x ⦄ := by
  rw [misc.raw.int.RawInt.new_eq]; exact (WP.spec_ok _).mpr rfl

@[local step]
private theorem const_new_ok {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t ⦃ r => r.1 = t ⦄ := by
  rw [misc.raw._const.Const.new_eq]; exact (WP.spec_ok _).mpr rfl

@[local step]
private theorem bitmap_rawbytes_new_ok (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    misc.raw.bytes.RawBytes.new (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 8192#usize)
      (core.convert.IntoFrom (core.convert.FromSame (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))) c
      ⦃ r => r.1 = c ⦄ := by
  rw [misc.raw.bytes.RawBytes.new_eq _ _ c c rfl]; exact (WP.spec_ok _).mpr rfl

private theorem build_loop_spec (params : Slice value.Value) (k : Usize)
    (bm : packets.NullBitmap value.ClientSide (alloc.vec.Vec U8)) (dl : Usize)
    (hk : k.val ≤ params.length)
    (hbl : bm.1.length = nullBitmapLen 0 params.length)
    (hbits : ∀ pos, bitAt bm.1.val pos = ((nullsOf params.val).take k.val).getD pos false)
    (hdl : dl.val = ((lensOf params.val).take k.val).sum)
    (hmax : (lensOf params.val).sum ≤ Usize.max) :
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
      simp only [lift, Aeneas.Std.bind_ok]
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
          rw [hbm1b pos, hoffv, Nat.add_zero, hi1, getD_take_succ _ _ _ _ hlenN]
          by_cases hp : pos = it.start.val
          · simp only [hp, ite_true, hnget, hnull]
          · simp only [hp, ite_false, hb4]
        · rw [hi1, hs1, hget, ← hd5]; omega
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
          rw [hi1, getD_take_succ _ _ _ _ hlenN, hb4]
          by_cases hp : pos = it.start.val
          · simp only [hp, ite_true, hnget, hnn, hold]
          · simp only [hp, ite_false]
        · rw [hi1, hs1, hget, hd1, hd5, hxv]
  · exact ⟨rfl, hk, hbl, hbits, hdl⟩

/-- `build(params)`: the request for the statement with no cursor, iteration count 1, the NULL bitmap of the parameters (offset 0; a parameter is NULL iff its binary encoding is empty), new-params-bound flag 1 and the parameters; `as_long_data` (also returned) iff the length the builder computes exceeds `MAX_PAYLOAD_LEN`. (The bound keeps that computation from overflowing.) -/
theorem packets.ComStmtExecuteRequestBuilder.build_spec (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value)
    (h : stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    packets.ComStmtExecuteRequestBuilder.build self params ⦃ req b =>
      req.stmt_id.1 = self.stmt_id ∧ req.flags.1.val = 0 ∧
      cowList req.bitmap.1 = nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v))) ∧
      req.params_flags.1.val = 1 ∧ req.params = params ∧ req.as_long_data = b ∧
      (b = true ↔ maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue)) ⦄ := by
  have hoffv := value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
  have hlenp : (params.val.map Val.ofValue).length = params.length := by simp
  simp only [stmtExecuteLen, hlenp, List.map_map] at h
  have hsum : (lensOf params.val).sum = (List.map ((fun v => (binEnc v).length) ∘ Val.ofValue) params.val).sum := rfl
  simp only [Slice.length] at h
  have hn' : params.val.length + 7 ≤ Usize.max := by omega
  unfold packets.ComStmtExecuteRequestBuilder.build
  step with packets.NullBitmap.bitmap_len_spec value.ClientSide.Insts.Mysql_commonValueSerializationSide _
    value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET rfl (Slice.len params)
    (by rw [hoffv]; simpa using hn') as ⟨bl, hbl⟩
  step*
  have hbm1 : bitmap.1 = v := ‹_›
  have hvv : v.val = List.replicate bl.val 0#u8 := ‹_›
  have hbl' : bl.val = nullBitmapLen 0 params.val.length := by rw [hbl, hoffv]; simp
  have hmax : (lensOf params.val).sum ≤ Usize.max := by rw [hsum]; omega
  apply WP.spec_bind (build_loop_spec params 0#usize bitmap 0#usize (by simp)
    (by rw [hbm1]; simp [alloc.vec.Vec.length, hvv, hbl'])
    (by intro pos; rw [hbm1, hvv]; simp only [bitAt, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> simp [mysql_common.PBUtil.byte_val])
    (by simp) hmax)
  rintro ⟨⟨bb, pd⟩, dl'⟩ ⟨hL, hB, hD⟩
  show (do
    let i3 ← 10#usize + bl
    let i4 ← i3 + 1#usize
    let i5 ← i4 + meta_len
    let total_len ← i5 + dl'
    let cu ← misc.raw.int.ConstU8.new packets.InvalidComStmtExecuteHeader 23#u8
    let ri ← misc.raw.int.RawInt.new misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 self.stmt_id
    let c ← misc.raw._const.Const.new U8 constants.CursorType.CURSOR_TYPE_NO_CURSOR
    let cu1 ← misc.raw.int.ConstU32.new packets.InvalidIterationCount 1#u32
    let c1 ← misc.raw._const.Const.new U8 constants.StmtExecuteParamsFlags.NEW_PARAMS_BOUND
    let rb ← misc.raw.bytes.RawBytes.new (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 8192#usize)
        (core.convert.IntoFrom (core.convert.FromSame (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))))
        (alloc.borrow.Cow.Owned bb)
    ok ((⟨cu, ri, c, cu1, rb, c1, params, decide (total_len > constants.MAX_PAYLOAD_LEN)⟩ :
        packets.ComStmtExecuteRequest), decide (total_len > constants.MAX_PAYLOAD_LEN))) ⦃ _ ⦄
  have hL' : bb.length = nullBitmapLen 0 params.val.length := hL
  have hB' : ∀ pos, bitAt bb.val pos = (nullsOf params.val).getD pos false := hB
  have hlen' : (Slice.len params).val = params.val.length := by simp [Slice.len]
  step*
  have hns := nullBitmap_spec 0 (params.val.map (fun v => isNullVal (Val.ofValue v)))
  have hmp : constants.MAX_PAYLOAD_LEN.val = maxPayloadLen := by
    simp [constants.MAX_PAYLOAD_LEN, maxPayloadLen]
  refine ⟨by simp_all, by rw [‹c.1 = constants.CursorType.CURSOR_TYPE_NO_CURSOR›]; simp [constants.CursorType.CURSOR_TYPE_NO_CURSOR], ?_,
    by rw [‹c1.1 = constants.StmtExecuteParamsFlags.NEW_PARAMS_BOUND›]; simp [constants.StmtExecuteParamsFlags.NEW_PARAMS_BOUND], ?_⟩
  · rw [rb_post]
    show bb.val = _
    apply bytes_ext_bits
    · rw [hns.1, List.length_map]; exact hL'
    · intro pos
      have := hns.2 pos
      simp only [bitmapBit, Nat.add_zero] at this
      rw [this, hB']
  · have ht : total_len.val = stmtExecuteLen (params.val.map Val.ofValue) := by
      simp only [stmtExecuteLen, hlenp, List.map_map]
      simp only [Slice.length] at hlenp
      rw [total_len_post, i5_post, i4_post, i3_post, meta_len_post, hbl', hD, hsum, hlen']
      simp [Slice.length]; ring
    simp only [decide_eq_true_eq, gt_iff_lt, UScalar.lt_equiv, hmp, ht]

private theorem paramType_length (v : Val) : (paramType v).length = 2 := by
  cases v <;> rfl

private theorem paramValue_length_le (ld : Bool) (v : Val) : (paramValue ld v).length ≤ (binEnc v).length := by
  cases v <;> simp [paramValue]; split <;> simp

private theorem types_length (l : List Val) : ((l.map paramType).flatten).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons v l ih => simp [paramType_length] at ih ⊢; omega

private theorem values_length_le (ld : Bool) (l : List Val) :
    ((l.map (paramValue ld)).flatten).length ≤ (l.map (fun v => (binEnc v).length)).sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    have := paramValue_length_le ld v
    omega

/-- Headline: `build` then `serialize` appends the protocol's `COM_STMT_EXECUTE` packet (`comStmtExecute`), with the `Bytes` values left out iff `as_long_data`, for at most 65536 parameters (beyond, the bitmap is truncated). -/
theorem packets.ComStmtExecuteRequestBuilder.build_serialize (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value) (buf : alloc.vec.Vec U8)
    (hn : params.length ≤ 65536) (h : buf.length + stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    (packets.ComStmtExecuteRequestBuilder.build self params >>= fun p =>
      packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize p.1 buf) ⦃ buf' =>
      buf'.val = buf.val ++ comStmtExecute self.stmt_id.val (params.val.map Val.ofValue)
        (decide (maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue))) ⦄ := by
  have hlenp : (params.val.map Val.ofValue).length = params.length := by simp
  have hbm : nullBitmapLen 0 params.length ≤ 8192 := by simp only [nullBitmapLen]; omega
  apply WP.spec_bind (packets.ComStmtExecuteRequestBuilder.build_spec self params (by omega))
  rintro ⟨req, b⟩ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp only at h1 h2 h3 h4 h5 h6 h7 ⊢
  have hns := nullBitmap_spec 0 (params.val.map (fun v => isNullVal (Val.ofValue v)))
  have hnsl : (nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v)))).length =
      nullBitmapLen 0 params.length := by rw [hns.1, List.length_map]
  have hbits : (cowList req.bitmap.1).take 8192 = nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v))) := by
    rw [h3]
    apply List.take_of_length_le
    rw [hnsl]; exact hbm
  have hlenB : (stmtExecuteBytes req.stmt_id.1.val req.flags.1.val ((cowList req.bitmap.1).take 8192)
      req.params_flags.1.val (req.params.val.map Val.ofValue) req.as_long_data).length ≤
      stmtExecuteLen (params.val.map Val.ofValue) := by
    rw [hbits, h5]
    have hT := types_length (params.val.map Val.ofValue)
    have hV := values_length_le req.as_long_data (params.val.map Val.ofValue)
    unfold stmtExecuteBytes stmtExecuteLen
    split <;> simp only [List.length_append, List.length_cons, List.length_nil, hT, hnsl,
      mysql_common.PBUtil.length_leBytes, hlenp] <;> omega
  apply WP.spec_mono (packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec req buf
    (by omega))
  intro buf' hb'
  rw [hb', hbits, h5, h1, h2, h4, h6]
  have : b = decide (maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue)) := by
    cases b <;> simp_all
  rw [this]
  simp [comStmtExecute, List.map_map, Function.comp_def]

end mysql_common
