import Defs
import Proofs.Value.ValueDeserializer
import Proofs.Packets.NullBitmap
import Proofs.Io.ParseBuf
import Proofs.Defs.Lemmas
import Proofs.Defs.LemmasCF

/-! Statements for `struct RowDeserializer and its impls` (spec file: `Specs/Row.lean`). Helper lemmas are private to this file. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ## Helpers -/

/-- Prepends decoded values to a decoding result. -/
private def preRead (ws : List Val) (p : Option (List Val) × List U8) : Option (List Val) × List U8 :=
  (p.1.map (ws ++ ·), p.2)

private theorem text_loop_spec (h64 : Target64) (n : Usize) (buf0 : io.ParseBuf) (iter : core.ops.range.Range Usize) (buf : io.ParseBuf)
    (values : alloc.vec.Vec (Option value.Value)) (ws : List Val)
    (hend : iter.end = n) (hs : iter.start.val ≤ n.val)
    (hv : values.val.map (Option.map Val.ofValue) = ws.map some) (hl : values.length = iter.start.val)
    (hr : textRowRead n.val buf0.val = preRead ws (textRowRead (n.val - iter.start.val) buf.val)) :
    row.deserialize_text_values_loop iter buf values ⦃ r b =>
      (okPart r).map (fun v => v.val.map (Option.map Val.ofValue)) = (textRowRead n.val buf0.val).1.map (List.map some) ∧
      b.val = (textRowRead n.val buf0.val).2 ⦄ := by
  unfold row.deserialize_text_values_loop
  apply loop.spec_decr_nat (fun (x : core.ops.range.Range Usize × io.ParseBuf × alloc.vec.Vec (Option value.Value)) => n.val - x.1.start.val)
    (fun x => ∃ ws : List Val, x.1.end = n ∧ x.1.start.val ≤ n.val ∧
      x.2.2.val.map (Option.map Val.ofValue) = ws.map some ∧ x.2.2.length = x.1.start.val ∧
      textRowRead n.val buf0.val = preRead ws (textRowRead (n.val - x.1.start.val) x.2.1.val))
  · rintro ⟨it, b, vs⟩ ⟨ws, hend, hs, hv, hl, hr⟩
    unfold row.deserialize_text_values_loop.body
    simp only at hend hs hv hl hr
    step*
    · have hge : ¬ it.start.val < it.end.val := by intro h; simp [h] at o_post; simp_all
      have heq : n.val - it.start.val = 0 := by subst hend; omega
      rw [heq] at hr
      simp [textRowRead, preRead] at hr
      simp [okPart, hr, hv]
    · have hlt : it.start.val < it.end.val := by
        by_contra h; simp [h] at o_post; simp_all
      simp [hlt] at o_post
      step with value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64
      have hk : n.val - it.start.val = (n.val - it.start.val - 1) + 1 := by subst hend; omega
      rw [hk] at hr
      simp only [textRowRead] at hr
      rcases r with ⟨v, ph⟩ | e
      · have e1 : (okPart (core.result.Result.Ok (v, ph) : core.result.Result (value.ValueDeserializer value.TextValue) core.io.error.Error)).map (fun d => Val.ofValue d.1) = some (Val.ofValue v) := rfl
        rw [e1] at r_post
        rw [← r_post] at hr
        simp only at hr
        step*
        subst cf_post
        rename_i hcf
        injection hcf with hcf
        subst hcf
        step*
        have hs1 : iter1.start.val = it.start.val + 1 := o_post.2
        refine ⟨⟨ws ++ [Val.ofValue v], by rw [o_post1, hend], by omega, ?_, ?_, ?_⟩, by omega⟩
        · rw [values1_post, List.map_append, hv, List.map_append]; rfl
        · simp [values1_post, hl, hs1]
        · rw [hr]
          have : n.val - iter1.start.val = n.val - it.start.val - 1 := by omega
          rw [this]
          rcases textRowRead (n.val - it.start.val - 1) buf1 with ⟨_ | _, _⟩ <;> simp [preRead, consRead]
      · have e1 : (okPart (core.result.Result.Err e : core.result.Result (value.ValueDeserializer value.TextValue) core.io.error.Error)).map (fun d => Val.ofValue d.1) = none := rfl
        rw [e1] at r_post
        rw [← r_post] at hr
        simp only at hr
        step*
        rw [hr, r1_post]
        simp [preRead, okPart]
  · exact ⟨ws, hend, hs, hv, hl, hr⟩

private theorem cow_as_ref (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    ∃ s : Slice U8, (alloc.borrow.Cow.Insts.CoreConvertAsRef
      (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)).as_ref c = ok s ∧ s.val = cowList c := by
  cases c <;> simp [alloc.borrow.Cow.Insts.CoreConvertAsRef.as_ref,
    alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref,
    alloc.vec.Vec.Insts.CoreBorrowBorrowSlice.borrow, cowList, alloc.vec.Vec.deref]

private theorem consRead_map (x : Val) (ws : List Val) (R : Option (List Val) × List U8) :
    (consRead x R).1.map (fun l => ws.map some ++ l.map some) =
      R.1.map (fun l => (ws ++ [x]).map some ++ l.map some) ∧ (consRead x R).2 = R.2 := by
  rcases R with ⟨_ | _, _⟩ <;> simp [consRead]

private theorem bin_values_spec (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (cols : Slice packets.Column)
    (bitmap : packets.NullBitmap S (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (bm : List U8)
    (hbm : cowList bitmap.1 = bm)
    (hlen : cols.length + 7 + off.val ≤ Usize.max) (hbl : bm.length = nullBitmapLen off.val cols.length)
    (hsup : ∀ (j : Nat) (c : packets.Column), cols.val[j]? = some c → binSupported c.column_type.1 = false →
      bitmapBit off.val bm j = true) (k : Nat) :
    ∀ (i : Usize) (buf : io.ParseBuf) (values : alloc.vec.Vec (Option value.Value)) (ws : List Val),
      k = cols.length - i.val → i.val ≤ cols.length → values.length = i.val →
      values.val.map (Option.map Val.ofValue) = ws.map some →
      row.deserialize_bin_values inst cols bitmap buf i values ⦃ r rest =>
        (okPart r).map (fun v => v.val.map (Option.map Val.ofValue)) =
          (binValuesRead off.val bm ((cols.val.drop i.val).map colInfo) i.val buf.val).1.map
            (fun l => ws.map some ++ l.map some) ∧
        rest.val = (binValuesRead off.val bm ((cols.val.drop i.val).map colInfo) i.val buf.val).2 ⦄ := by
  obtain ⟨s, hs, hsv⟩ := cow_as_ref bitmap.1
  induction k with
  | zero =>
    intro i buf values ws hk hi hl hv
    unfold row.deserialize_bin_values
    have hd : cols.val.drop i.val = [] := by simp [Slice.length] at *; omega
    step*
    simp [hd, binValuesRead, okPart, hv]
  | succ k ih =>
    intro i buf values ws hk hi hl hv
    unfold row.deserialize_bin_values
    have hlt : i.val < cols.length := by omega
    have hsl : s.length = nullBitmapLen off.val cols.length := by
      rw [← hbl, ← hbm, ← hsv]
    have hd : cols.val.drop i.val = cols.val[i.val]'(by simpa [Slice.length] using hlt) :: cols.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons _
    step*
    step with packets.NullBitmap.is_null_spec inst _ off hoff bitmap s hs i (by omega)
      (by rw [hsl]; unfold nullBitmapLen; omega)
    rw [hsv, hbm] at b_post
    rw [hd]
    simp only [List.map_cons, colInfo, binValuesRead]
    subst b_post
    by_cases hb : bitmapBit off.val bm i.val = true
    · simp only [hb, ite_true]
      step; step
      refine WP.spec_mono (ih i2 buf values1 (ws ++ [Val.null]) (by omega) (by omega)
        (by simp [values1_post, hl, i2_post]) ?_) ?_
      · rw [values1_post, List.map_append, hv, List.map_append]; rfl
      · rintro ⟨r, rest⟩ ⟨h1, h2⟩
        rw [i2_post] at h1 h2
        exact ⟨by rw [h1, (consRead_map Val.null ws _).1], by rw [h2, (consRead_map Val.null ws _).2]⟩
    · simp only [hb, Bool.false_eq_true, ite_false]
      have hct : binSupported c.column_type.1 = true := by
        by_contra h
        exact hb (hsup i.val c (by rw [c_post]; exact List.getElem?_eq_getElem _) (by simpa using h))
      have e1 : packets.Column.impl.column_type c = ok c.column_type.1 := rfl
      have e2 : packets.Column.impl.flags c = ok c.flags.1 := rfl
      simp only [e1, e2]
      step with value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec h64 c.column_type.1 c.flags.1 hct as ⟨r, buf1, r_post⟩
      rw [← c_post, ← r_post]
      rcases r with ⟨v, ph⟩ | e
      · have e3 : (okPart (core.result.Result.Ok (v, ph) : core.result.Result (value.ValueDeserializer value.BinValue) core.io.error.Error)).map (fun d => Val.ofValue d.1) = some (Val.ofValue v) := rfl
        rw [e3]
        simp only
        step
        subst cf1_post
        simp only
        step as ⟨values1, values1_post⟩
        step as ⟨i2, i2_post⟩
        refine WP.spec_mono (ih i2 buf1 values1 (ws ++ [Val.ofValue v]) (by omega) (by omega)
          (by simp [values1_post, hl, i2_post]) ?_) ?_
        · rw [values1_post, List.map_append, hv, List.map_append]; rfl
        · rintro ⟨r, rest⟩ ⟨h1, h2⟩
          rw [i2_post] at h1 h2
          exact ⟨by rw [h1, (consRead_map (Val.ofValue v) ws _).1], by rw [h2, (consRead_map (Val.ofValue v) ws _).2]⟩
      · have e3 : (okPart (core.result.Result.Err e : core.result.Result (value.ValueDeserializer value.BinValue) core.io.error.Error)).map (fun d => Val.ofValue d.1) = none := rfl
        rw [e3]
        simp only
        step*
        simp [r1_post, okPart]

private theorem bin_spec (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hsup : ∀ (i : Nat) (c : packets.Column), columns.val[i]? = some c → binSupported c.column_type.1 = false →
      bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) i = true) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead off.val (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead off.val (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  unfold row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize
  step as ⟨o, buf1, o_post⟩
  rcases hb : buf.val with _ | ⟨hd, tl⟩
  · have : ¬ 1 ≤ buf.length := by simp [Slice.length, hb]
    simp only [this, ite_false] at o_post
    obtain ⟨rfl, rfl⟩ := o_post
    unfold misc.unexpected_buf_eof misc.io_error_msg
    step*
    simp [binRowRead, okPart, hb]
  · have h1 : 1 ≤ buf.length := by simp [Slice.length, hb]
    simp only [h1, ite_true, hb] at o_post
    obtain ⟨ho, hbuf1⟩ := o_post
    rcases o with _ | x
    · simp at ho
    simp only [List.drop_succ_cons, List.drop_zero] at hbuf1
    simp only [hb, List.drop_succ_cons, List.drop_zero] at hsup
    simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
    step with packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec inst off hoff (Slice.len columns) (by simpa using hlen) as ⟨r, buf2, r_post⟩
    simp only [binRowRead, List.length_map]
    have hl1 : buf1.length = tl.length := by simp [Slice.length, hbuf1]
    have hcl : (Slice.len columns).val = columns.val.length := by simp
    split_ifs at r_post with hk
    · have hk' : ¬ tl.length < nullBitmapLen off.val columns.val.length := by rw [hcl] at hk; omega
      rw [hcl, hbuf1] at r_post
      simp only [hk', ite_false]
      obtain ⟨hr, hbuf2⟩ := r_post
      rcases r with nb0 | e
      · simp only [okPart, Option.map_some, Option.some.injEq] at hr
        step*
        subst cf_post
        rename_i hcf
        injection hcf with hcf
        subst hcf
        have hw : (alloc.vec.Vec.with_capacity (Option value.Value) (Slice.len columns)).val = [] := by
          simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
        step with bin_values_spec h64 inst off hoff columns nb0 _ hr hlen
          (by rw [List.length_take]; simp only [Slice.length]; omega) hsup columns.length 0#usize buf2
          (alloc.vec.Vec.with_capacity (Option value.Value) (Slice.len columns)) [] (by simp)
          (by simp) (by simp [alloc.vec.Vec.length, hw]) (by simp [hw]) as ⟨r1, buf3, h1, h2⟩
        simp only [List.drop_zero, List.map_nil, List.nil_append] at h1 h2
        rw [hbuf2] at h1 h2
        rcases r1 with vals | e
        · step*
          subst cf1_post
          rename_i hcf
          injection hcf with hcf
          subst hcf
          refine ⟨?_, h2, ?_⟩
          · simp only [okPart, Option.map_some] at h1 ⊢
            rw [← h1]; rfl
          · intro d hd; simp only [okPart] at hd; injection hd with hd; subst hd; rfl
        · step*
          simp only [okPart, Option.map_none] at h1 ⊢
          refine ⟨?_, h2, by simp [r2_post]⟩
          rw [r2_post]; rw [← h1]; rfl
      · simp [okPart] at hr
    · have hk' : tl.length < nullBitmapLen off.val columns.val.length := by rw [hcl] at hk; omega
      simp only [hk', ite_true]
      obtain ⟨hr, rfl⟩ := r_post
      rcases r with nb | e
      · simp [okPart] at hr
      · step*
        simp [r1_post, okPart, hbuf1]

private theorem isNullVal_iff (v : Val) : isNullVal v = true ↔ v = .null := by
  cases v <;> simp [isNullVal]

private theorem binValuesRead_enc (off : Nat) (bm : List U8)
    (E : value.Value → packets.Column → List U8) (F : value.Value → packets.Column → Val)
    (hE : ∀ v c, Val.ofValue v = .null → E v c = []) (hF : ∀ v c, Val.ofValue v = .null → F v c = .null)
    (tail : List U8) :
    ∀ (vs : List value.Value) (cs : List packets.Column) (i : Nat), vs.length = cs.length →
      (∀ j (hj : j < vs.length), bitmapBit off bm (i + j) = isNullVal (Val.ofValue vs[j])) →
      (∀ p ∈ vs.zip cs, Val.ofValue p.1 ≠ .null → ∀ t,
        binRead (colInfo p.2).1 (colInfo p.2).2 (E p.1 p.2 ++ t) = (some (F p.1 p.2), t)) →
      binValuesRead off bm (cs.map colInfo) i ((List.zipWith E vs cs).flatten ++ tail) =
        (some (List.zipWith F vs cs), tail)
  | [], [], _, _, _, _ => by simp [binValuesRead]
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | v :: vs, c :: cs, i, hl, hbit, H => by
    have ih := binValuesRead_enc off bm E F hE hF tail vs cs (i + 1) (by simpa using hl)
      (fun j hj => by have := hbit (j + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      (fun p hp => H p (by simp [hp]))
    have h0 := hbit 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    simp only [List.map_cons, List.zipWith_cons_cons, List.flatten_cons, binValuesRead]
    by_cases hn : Val.ofValue v = .null
    · rw [h0, (isNullVal_iff _).2 hn]
      simp only [↓reduceIte]
      rw [hE v c hn, List.nil_append, ih, hF v c hn]
      rfl
    · have hb : isNullVal (Val.ofValue v) = false := by
        cases h : isNullVal (Val.ofValue v)
        · rfl
        · exact absurd ((isNullVal_iff _).1 h) hn
      rw [h0, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hr := H (v, c) (by simp) hn ((List.zipWith E vs cs).flatten ++ tail)
      simp only [colInfo] at hr ⊢
      rw [List.append_assoc, hr]
      dsimp only
      rw [ih]; rfl

private theorem binRowRead_enc (off : Nat)
    (E : value.Value → packets.Column → List U8) (F : value.Value → packets.Column → Val)
    (hE : ∀ v c, Val.ofValue v = .null → E v c = []) (hF : ∀ v c, Val.ofValue v = .null → F v c = .null)
    (tail : List U8) (vs : List value.Value) (cs : List packets.Column) (hl : vs.length = cs.length)
    (H : ∀ p ∈ vs.zip cs, Val.ofValue p.1 ≠ .null → ∀ t,
        binRead (colInfo p.2).1 (colInfo p.2).2 (E p.1 p.2 ++ t) = (some (F p.1 p.2), t)) :
    binRowRead off (cs.map colInfo)
      ((byte 0 :: nullBitmap off ((vs.map Val.ofValue).map isNullVal) ++ (List.zipWith E vs cs).flatten) ++ tail) =
        (some (List.zipWith F vs cs), tail) := by
  obtain ⟨hlen, hbits⟩ := nullBitmap_spec off ((vs.map Val.ofValue).map isNullVal)
  rw [List.map_map] at hlen hbits
  simp only [List.length_map] at hlen
  simp only [binRowRead, List.cons_append, List.length_map, ← hl, List.append_assoc, List.map_map]
  have hnl : ¬ ((nullBitmap off (List.map (isNullVal ∘ Val.ofValue) vs) ++
      ((List.zipWith E vs cs).flatten ++ tail)).length < nullBitmapLen off vs.length) := by
    simp only [List.length_append, hlen]; omega
  simp only [hnl, ↓reduceIte]
  rw [← hlen, List.take_left, List.drop_left]
  apply binValuesRead_enc off _ E F hE hF tail vs cs 0 hl _ H
  intro j hj
  rw [Nat.zero_add, hbits]
  simp [List.getD_eq_getElem?_getD, hj]


private theorem binCompatible_supported (v : Val) (ct : constants.ColumnType) (h : binCompatible v ct) :
    binSupported ct = true := by
  cases v <;> simp only [binCompatible] at h
  case bytes => cases ct <;> simp_all [isLenencStrType, binSupported]
  case date => rcases h with h | h | h | h <;> subst h <;> rfl
  all_goals (subst h; rfl)

private theorem binFitsAt_supported (ct : constants.ColumnType) (u : Bool) (v : Val) (h : binFitsAt ct u v) :
    binSupported ct = true := by
  unfold binFitsAt at h
  cases hw : intWidth ct with
  | none => rw [hw] at h; exact binCompatible_supported v ct h
  | some k => cases ct <;> simp_all [intWidth, binSupported]

private theorem roundtrip_core (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (E : value.Value → packets.Column → List U8) (F : value.Value → packets.Column → Val)
    (hE : ∀ v c, Val.ofValue v = .null → E v c = []) (hF : ∀ v c, Val.ofValue v = .null → F v c = .null)
    (H : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 ≠ .null → ∀ t,
        binRead (colInfo p.2).1 (colInfo p.2).2 (E p.1 p.2 ++ t) = (some (F p.1 p.2), t))
    (hS : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 ≠ .null → binSupported p.2.column_type.1 = true)
    (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = (byte 0 :: nullBitmap off.val ((vs.map Val.ofValue).map isNullVal) ++
      (List.zipWith E vs columns.val).flatten) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = some ((List.zipWith F vs columns.val).map some) ∧
      rest.val = tail ⦄ := by
  have hl : vs.length = columns.val.length := hn
  obtain ⟨hblen, hbits⟩ := nullBitmap_spec off.val ((vs.map Val.ofValue).map isNullVal)
  simp only [List.length_map] at hblen
  have hsup : ∀ (i : Nat) (c : packets.Column), columns.val[i]? = some c → binSupported c.column_type.1 = false →
      bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) i = true := by
    intro i c hc hns
    have hcl : nullBitmapLen off.val columns.length =
        (nullBitmap off.val ((vs.map Val.ofValue).map isNullVal)).length := by rw [hblen, hn]
    rw [h, hcl]
    simp only [List.cons_append, List.drop_one, List.tail_cons, List.append_assoc]
    rw [List.take_left, hbits]
    have hi : i < columns.val.length := by
      by_contra hh; rw [List.getElem?_eq_none (by omega)] at hc; cases hc
    have hci : columns.val[i] = c := by rw [List.getElem?_eq_getElem hi] at hc; exact Option.some.inj hc
    have hiv : i < vs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hiv]
    simp only [Option.map_some, Option.getD_some]
    rw [isNullVal_iff]
    by_contra hnn
    have hmem : (vs[i], c) ∈ vs.zip columns.val := by
      rw [← hci, List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    rw [hS _ hmem hnn] at hns; cases hns
  apply WP.spec_mono (bin_spec h64 inst off hoff columns hlen buf hsup)
  rintro ⟨r, rest⟩ ⟨h1, h2, _⟩
  rw [h, binRowRead_enc off.val E F hE hF tail vs columns.val hl H] at h1 h2
  exact ⟨by rw [h1]; rfl, h2⟩

private theorem zipWith_left {α β γ : Type} (g : α → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length → List.zipWith (fun x _ => g x) xs ys = xs.map g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by simp [zipWith_left g xs ys (by simpa using h)]

private theorem zipWith_swap_map {γ : Type} (g : constants.ColumnType → Val → γ) :
    ∀ (vs : List value.Value) (cs : List packets.Column),
      List.zipWith g (cs.map (·.column_type.1)) (vs.map Val.ofValue) =
        List.zipWith (fun v c => g c.column_type.1 (Val.ofValue v)) vs cs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | v :: vs, c :: cs => by simp [zipWith_swap_map g vs cs]

private theorem map_zip_eq {γ : Type} (F : value.Value → packets.Column → γ) :
    ∀ (vs : List value.Value) (cs : List packets.Column),
      (vs.zip cs).map (fun p => some (F p.1 p.2)) = (List.zipWith F vs cs).map some
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | v :: vs, c :: cs => by simp [map_zip_eq F vs cs]

/-! ## Statements -/

/-- `into_inner`: the row. -/
theorem row.RowDeserializer.into_inner_eq {S P : Type} (self : row.RowDeserializer S P) :
    row.RowDeserializer.into_inner self = ok self.1 := by
  unfold row.RowDeserializer.into_inner; rfl

/-- `MyDeserialize for RowDeserializer<T, Text>`: `SIZE` is `None`. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq (T : Type) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE T = none := by
  unfold row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE; rfl

/-- `MyDeserialize for RowDeserializer<T, Text>`: total; one text value per column (`textRowRead`), all present (`Some`), with the given columns. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column))
    (buf : io.ParseBuf) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = (textRowRead columns.length buf.val).1.map (List.map some) ∧
      rest.val = (textRowRead columns.length buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  unfold row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize row.deserialize_text_values
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
  have hw : (alloc.vec.Vec.with_capacity (Option value.Value) (Slice.len columns)).val = [] := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  step with text_loop_spec h64 (Slice.len columns) buf { start := 0#usize, «end» := Slice.len columns } buf
    (alloc.vec.Vec.with_capacity (Option value.Value) (Slice.len columns)) [] rfl (by simp)
    (by simp [hw]) (by simp [alloc.vec.Vec.length, hw]) (by simp [preRead]) as ⟨rb, h1, h2⟩
  obtain ⟨r, buf1⟩ := rb
  simp only at h1 h2 ⊢
  have hcl : (Slice.len columns).val = Slice.length columns := by simp
  rw [hcl] at h1 h2
  rcases r with vals | e
  · step*
    subst cf_post
    rename_i hcf
    injection hcf with hcf
    subst hcf
    refine ⟨?_, h2, ?_⟩
    · simp only [okPart, Option.map_some] at h1 ⊢
      rw [← h1]; rfl
    · intro d hd; simp only [okPart] at hd; injection hd with hd; subst hd; rfl
  · step*
    simp only [okPart, Option.map_none] at h1 ⊢
    refine ⟨?_, h2, by simp [r1_post]⟩
    rw [r1_post]; rw [← h1]; rfl

/-- Round trip: a text row of `NULL`s and byte strings (one per column) is read back. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column)) (vs : List Val)
    (hv : ∀ v ∈ vs, isTextVal v = true) (hn : vs.length = columns.length) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = (vs.map textEnc).flatten ++ tail) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = some (vs.map some) ∧ rest.val = tail ⦄ := by
  have hs : ∀ s, Val.bytes s ∈ vs → s.length < 2 ^ 64 := by
    intro s hs
    have hm : textEnc (Val.bytes s) ∈ vs.map textEnc := List.mem_map_of_mem hs
    have h1 : (textEnc (Val.bytes s)).length ≤ ((vs.map textEnc).flatten).length :=
      (List.sublist_flatten_of_mem hm).length_le
    have h2 : s.length ≤ (textEnc (Val.bytes s)).length := by simp [textEnc, lenencStr]
    have h3 : buf.val.length ≤ Usize.max := buf.property
    have h4 : ((vs.map textEnc).flatten).length ≤ buf.val.length := by rw [h]; simp
    have h5 : Usize.max < 2 ^ 64 := by
      rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]
    omega
  have hr := textRowRead_textEnc vs hv hs tail
  apply WP.spec_mono (row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec h64 T columns buf)
  rintro ⟨r, rest⟩ ⟨h1, h2, _⟩
  have hcl : Slice.length columns = vs.length := hn.symm
  rw [hcl, h, hr] at h1 h2
  exact ⟨h1, h2⟩

/-- `MyDeserialize for RowDeserializer<S, Binary>`: `SIZE` is `None`. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq {S : Type} (inst : value.SerializationSide S) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE inst = none := by
  unfold row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE; rfl

/-- `MyDeserialize for RowDeserializer<S, Binary>`: when every column whose type the binary value decoder does not support is marked NULL in the row's bitmap, total; `binRowRead` with `S`'s bit offset (header byte, NULL bitmap, then the non-NULL values), all present (`Some`), with the given columns. (The bound on the number of columns keeps `bitmap_len` from overflowing.) -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hsup : ∀ (i : Nat) (c : packets.Column), columns.val[i]? = some c → binSupported c.column_type.1 = false →
      bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) i = true) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead off.val (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead off.val (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  exact bin_spec h64 inst off hoff columns hlen buf hsup

/-- **Crash path.** `MyDeserialize for RowDeserializer<S, Binary>` panics when it reaches a non-NULL value of a column of unsupported type; e.g. when the first column has such a type and is not marked NULL. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_unsupported {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (c : packets.Column) (cs : List packets.Column) (hc : columns.val = c :: cs)
    (hsup : binSupported c.column_type.1 = false)
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hbuf : 1 + nullBitmapLen off.val columns.length ≤ buf.length)
    (hnn : bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) 0 = false) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf = fail .panic := by
  have hb1 : 1 ≤ buf.length := by omega
  obtain ⟨⟨o, buf1⟩, he1, hp1⟩ := PBUtil.spec_eq_ok (io.ParseBuf.checked_eat_u8_spec buf)
  simp only [hb1, ite_true] at hp1
  obtain ⟨ho, hbuf1⟩ := hp1
  rcases o with _ | x
  · simp at ho
  have hcl : (Slice.len columns).val = Slice.length columns := by simp
  obtain ⟨⟨r, buf2⟩, he2, hp2⟩ := PBUtil.spec_eq_ok
    (packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec inst off hoff
      (Slice.len columns) (by rw [hcl]; exact hlen) buf1)
  have hk : nullBitmapLen off.val (Slice.len columns).val ≤ buf1.length := by
    rw [hcl]; simp only [Slice.length] at hbuf1 ⊢; rw [hbuf1, List.length_drop]; simp only [Slice.length] at hbuf; omega
  simp only [hk, ite_true] at hp2
  obtain ⟨hr, hbuf2⟩ := hp2
  rcases r with nb | e
  swap
  · simp [okPart] at hr
  simp only [okPart, Option.map_some, Option.some.injEq] at hr
  obtain ⟨s, hs, hsv⟩ := cow_as_ref nb.1
  have h0 : (0#usize : Usize).val = 0 := rfl
  have hsl : s.val.length = nullBitmapLen off.val (Slice.length columns) := by
    rw [hsv, hr, List.length_take, Nat.min_eq_left hk, hcl]
  have hpos : 0 < Slice.length columns := by simp [Slice.length, hc]
  obtain ⟨b, hnull, hbv⟩ := PBUtil.spec_eq_ok (packets.NullBitmap.is_null_spec inst _ off hoff nb s hs 0#usize
    (by rw [h0]; omega) (by
      have : s.length = s.val.length := rfl
      rw [this, hsl, h0]; unfold nullBitmapLen; omega))
  have hb : b = false := by
    rw [hbv, hsv, hr, hcl, hbuf1, h0]; simpa using hnn
  subst hb
  have hval := value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_unsupported
    c.column_type.1 c.flags.1 hsup buf2
  have hidx : Slice.index_usize columns 0#usize = ok c := by
    simp [Slice.index_usize, hc, h0]
  have hlt : (0#usize : Usize) < Slice.len columns := by scalar_tac
  have e1 : packets.Column.impl.column_type c = ok c.column_type.1 := rfl
  have e2 : packets.Column.impl.flags c = ok c.flags.1 := rfl
  have hdv : ∀ v, row.deserialize_bin_values inst columns nb buf2 0#usize v = fail .panic := by
    intro v
    unfold row.deserialize_bin_values
    simp [hlt, hidx, hnull, e1, e2, hval]
  unfold row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize
  simp [he1, he2, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.result.Result.Insts.CoreOpsTry.branch, hdv]

/-- Round trip (parameter encoding: every integer in 8 bytes, so integers only at `LONGLONG`; see `roundtrip_at` for the server's format): a binary row (`binRowEnc`: header, NULL bitmap, values) of `Value`s that are `NULL` or fit their column's type (`binCompatible`) is read back, up to the value decoder's normalisation `binNorm` (integers reinterpreted by the column's `UNSIGNED_FLAG`, negative zero times made positive). -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨ binCompatible (Val.ofValue p.1) p.2.column_type.1)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binRowEnc off.val (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p => some (binNorm (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄ := by
  have hl : vs.length = columns.val.length := hn
  have hm := roundtrip_core h64 inst off hoff columns hlen vs hn
    (fun v _ => binEnc (Val.ofValue v)) (fun v c => binNorm (isUnsigned c.flags.1) (Val.ofValue v))
    (fun v _ hv => by simp only [hv]; rfl) (fun v _ hv => by simp only [hv]; rfl)
    (fun p hp hnn t => by
      rcases hc p hp with h0 | h0
      · exact absurd h0 hnn
      · exact binRead_binEnc p.1 p.2.column_type.1 _ t h0)
    (fun p hp hnn => by
      rcases hc p hp with h0 | h0
      · exact absurd h0 hnn
      · exact binCompatible_supported _ _ h0)
    tail buf (by
      rw [h, binRowEnc, zipWith_left (fun v => binEnc (Val.ofValue v)) vs columns.val hl]; simp only [List.map_map]; rfl)
  apply WP.spec_mono hm
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  exact ⟨by rw [h1, map_zip_eq (fun v c => binNorm (isUnsigned c.flags.1) (Val.ofValue v))], h2⟩

/-- `ServerSide::BIT_OFFSET` is 2 (from `src/value/mod.rs`; the offset of binary result-set rows). -/
theorem value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val :
    value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET.val = 2 := by
  unfold value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET; rfl

/-- `MyDeserialize for RowDeserializer<ServerSide, Binary>` (how clients read binary result-set rows): `deserialize_spec` at bit offset 2. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec_server (h64 : Target64) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 9 ≤ Usize.max) (buf : io.ParseBuf)
    (hsup : ∀ (i : Nat) (c : packets.Column), columns.val[i]? = some c → binSupported c.column_type.1 = false →
      bitmapBit 2 ((buf.val.drop 1).take (nullBitmapLen 2 columns.length)) i = true) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize value.ServerSide.Insts.Mysql_commonValueSerializationSide columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead 2 (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead 2 (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  have h2 := value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
  have := bin_spec h64 value.ServerSide.Insts.Mysql_commonValueSerializationSide
    value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET rfl columns (by rw [h2]; omega) buf
    (by rw [h2]; exact hsup)
  rw [h2] at this; exact this

/-- Round trip at the columns' types: a binary row as the server sends it (`binRowEncAt`: each non-NULL value in its column's format, integers in the column's width) of `Value`s that are `NULL` or fit their column (`binFitsAt`: in range for a narrow integer type, else `binCompatible`) is read back, up to `binNormAt`. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨
      binFitsAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1))
    (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = binRowEncAt off.val (columns.val.map (·.column_type.1)) (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p =>
          some (binNormAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄ := by
  have hl : vs.length = columns.val.length := hn
  have hm := roundtrip_core h64 inst off hoff columns hlen vs hn
    (fun v c => binEncAt c.column_type.1 (Val.ofValue v))
    (fun v c => binNormAt c.column_type.1 (isUnsigned c.flags.1) (Val.ofValue v))
    (fun v c hv => by simp only [hv, binEncAt]; split <;> first | rfl | simp_all)
    (fun v c hv => by simp only [hv, binNormAt]; split <;> first | rfl | simp_all)
    (fun p hp hnn t => by
      rcases hc p hp with h0 | h0
      · exact absurd h0 hnn
      · exact binRead_binEncAt p.2.column_type.1 _ p.1 h0 t)
    (fun p hp hnn => by
      rcases hc p hp with h0 | h0
      · exact absurd h0 hnn
      · exact binFitsAt_supported _ _ _ h0)
    tail buf (by
      rw [h, binRowEncAt, zipWith_swap_map binEncAt vs columns.val])
  apply WP.spec_mono hm
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  exact ⟨by rw [h1, map_zip_eq (fun v c => binNormAt c.column_type.1 (isUnsigned c.flags.1) (Val.ofValue v))], h2⟩

/-- `roundtrip_at` at `ServerSide` (bit offset 2). -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at_server (h64 : Target64) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 9 ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨
      binFitsAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1))
    (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = binRowEncAt 2 (columns.val.map (·.column_type.1)) (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize value.ServerSide.Insts.Mysql_commonValueSerializationSide columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p =>
          some (binNormAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄ := by
  have h2 := value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
  have := row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at h64
    value.ServerSide.Insts.Mysql_commonValueSerializationSide
    value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET rfl columns (by rw [h2]; omega) vs hn hc tail buf
    (by rw [h2]; exact h)
  exact this

end mysql_common
