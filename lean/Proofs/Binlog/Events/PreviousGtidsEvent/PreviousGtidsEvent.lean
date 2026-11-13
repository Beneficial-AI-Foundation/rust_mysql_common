import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct PreviousGtidsEvent and its impls` (spec file: `Specs/Binlog/Events/PreviousGtidsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(sids)`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.new_eq (ss : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.new ss = ok { sids := ss } := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.new; rfl

private theorem sids_into_owned_none (n : Nat) :
    ∀ (v : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid), v.val.length = n → (∀ s ∈ v.val, s.tag = none) →
      binlog.events.previous_gtids_event.sids_into_owned v ⦃ v' => v'.val = v.val ⦄ := by
  induction n with
  | zero =>
    intro v hl _
    unfold binlog.events.previous_gtids_event.sids_into_owned
    have : v.val = [] := List.length_eq_zero_iff.1 hl
    simp [alloc.vec.Vec.pop, this, alloc.vec.Vec.new]
  | succ n ih =>
    intro v hl hn
    obtain ⟨l, x, hlx⟩ : ∃ l x, v.val = l ++ [x] := by
      rcases List.eq_nil_or_concat v.val with h | ⟨l, x, h⟩
      · rw [h] at hl; simp at hl
      · exact ⟨l, x, by rw [h, List.concat_eq_append]⟩
    unfold binlog.events.previous_gtids_event.sids_into_owned
    simp only [alloc.vec.Vec.pop, hlx, List.getLast?_concat, List.dropLast_concat]
    have hx : x.tag = none := hn x (by simp [hlx])
    have hl' : l.length = n := by rw [hlx] at hl; simpa using hl
    have hmax : v.val.length ≤ Usize.max := v.property
    step with ih (alloc.vec.Vec.from l (by rw [hlx] at hmax; simp at hmax; omega)) (by simpa using hl')
      (fun s hs => hn s (by rw [hlx]; exact List.mem_append_left _ (by simpa using hs))) as ⟨w, hw⟩
    simp only [binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned, hx]
    step*


/-! ### Serialization helpers -/

private theorem gno_serialize (g : packets.GnoInterval) (buf : alloc.vec.Vec U8) (h : buf.length + 16 ≤ Usize.max) :
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize g buf ⦃ b' => b'.val = buf.val ++ gnoIntervalEnc g ⦄ := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize
  step*
  · simp [alloc.vec.Vec.length, *, length_leBytes]
  · simp_all [gnoIntervalEnc]

private theorem gnoIntervalEnc_length (g : packets.GnoInterval) : (gnoIntervalEnc g).length = 16 := by
  simp [gnoIntervalEnc, length_leBytes]

private theorem flatten_gno_length (l : List packets.GnoInterval) : (l.map gnoIntervalEnc).flatten.length = 16 * l.length := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, gnoIntervalEnc_length, List.length_cons]; ring

private theorem serialize_intervals_spec (ints : Slice packets.GnoInterval) (k : Nat) :
    ∀ (j : Usize) (buf : alloc.vec.Vec U8), ints.length - j.val = k → j.val ≤ ints.length →
      buf.length + 16 * (ints.length - j.val) ≤ Usize.max →
      binlog.events.previous_gtids_event.serialize_intervals ints j buf ⦃ b' => b'.val = buf.val ++ ((ints.val.drop j.val).map gnoIntervalEnc).flatten ⦄ := by
  induction k with
  | zero =>
    intro j buf hk hj _
    unfold binlog.events.previous_gtids_event.serialize_intervals
    simp only [Slice.length] at *
    have hd : ints.val.length ≤ j.val := by omega
    split_ifs with hlt
    · exfalso; scalar_tac
    · simp [List.drop_of_length_le hd]
  | succ k ih =>
    intro j buf hk hj hb
    unfold binlog.events.previous_gtids_event.serialize_intervals
    have hlt : j.val < ints.length := by omega
    step*
    step with gno_serialize gi buf (by simp only [Slice.length] at *; omega) as ⟨b1, hb1⟩
    step as ⟨i1, hi1⟩
    have hb1l : b1.length = buf.length + 16 := by simp [alloc.vec.Vec.length, hb1, gnoIntervalEnc_length]
    apply WP.spec_mono (ih i1 b1 (by scalar_tac) (by scalar_tac) (by rw [hb1l]; scalar_tac))
    intro b2 hb2
    rw [hb2, hb1, List.append_assoc]
    congr 1
    have hlt' : j.val < ints.val.length := hlt
    rw [hi1, List.drop_eq_getElem_cons (i := j.val) hlt', gi_post]
    simp only [List.map_cons, List.flatten_cons]


private theorem pgSidEnc_length (x : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    (pgSidEnc x).length = 24 + 16 * x.intervals.length := by
  simp only [pgSidEnc, List.length_append, length_leBytes, flatten_gno_length]
  have : x.uuid.val.length = 16 := by simp
  simp only [alloc.vec.Vec.length]; omega

private theorem serialize_sid_spec (x : binlog.events.previous_gtids_event.PreviousGtidsSid) (buf : alloc.vec.Vec U8)
    (h : buf.length + (pgSidEnc x).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.serialize_sid x false buf ⦃ b' => b'.val = buf.val ++ pgSidEnc x ⦄ := by
  rw [pgSidEnc_length] at h
  unfold binlog.events.previous_gtids_event.serialize_sid binlog.events.previous_gtids_event.serialize_sid_tag
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hu : x.uuid.val.length = 16 := by simp
  step*
  · have : buf2.length = buf.length + 16 := by simp [alloc.vec.Vec.length, buf2_post, s_post, hu]
    simp only [Slice.length, s1_post, a_post, length_leBytes, this]; omega
  · have hl3 : buf3.length = buf.length + 24 := by
      simp [alloc.vec.Vec.length, buf3_post, buf2_post, s_post, hu, s1_post, a_post, length_leBytes]
    have := serialize_intervals_spec (alloc.vec.Vec.deref x.intervals) _ 0#usize buf3 rfl (by simp) (by
      rw [hl3]; simp [alloc.vec.Vec.deref, Slice.length]; simp only [alloc.vec.Vec.length] at h; omega)
    apply WP.spec_mono this
    intro b hb
    have hi : i1.val = x.intervals.length := by simp [i1_post]
    simp only [hb, buf3_post, buf2_post, s_post, s1_post, a_post, hi, pgSidEnc, List.append_assoc]
    simp [alloc.vec.Vec.deref]

private theorem serialize_sids_spec (sids : Slice binlog.events.previous_gtids_event.PreviousGtidsSid) (k : Nat) :
    ∀ (i : Usize) (buf : alloc.vec.Vec U8), sids.length - i.val = k → i.val ≤ sids.length →
      buf.length + ((sids.val.drop i.val).map pgSidEnc).flatten.length ≤ Usize.max →
      binlog.events.previous_gtids_event.serialize_sids sids i false buf ⦃ b' => b'.val = buf.val ++ ((sids.val.drop i.val).map pgSidEnc).flatten ⦄ := by
  induction k with
  | zero =>
    intro i buf hk hi _
    unfold binlog.events.previous_gtids_event.serialize_sids
    simp only [Slice.length] at *
    have hd : sids.val.length ≤ i.val := by omega
    split_ifs with hlt
    · exfalso; scalar_tac
    · simp [List.drop_of_length_le hd]
  | succ k ih =>
    intro i buf hk hi hb
    unfold binlog.events.previous_gtids_event.serialize_sids
    have hlt : i.val < sids.length := by omega
    have hlt' : i.val < sids.val.length := hlt
    rw [List.drop_eq_getElem_cons (i := i.val) hlt'] at hb ⊢
    simp only [List.map_cons, List.flatten_cons, List.length_append] at hb ⊢
    step*
    step with serialize_sid_spec pgs buf (by rw [pgs_post]; omega) as ⟨b1, hb1⟩
    step as ⟨i2, hi2⟩
    have hb1l : b1.length = buf.length + (pgSidEnc sids.val[i.val]).length := by
      simp only [alloc.vec.Vec.length, hb1, List.length_append, pgs_post]; rfl
    apply WP.spec_mono (ih i2 b1 (by scalar_tac) (by scalar_tac) (by rw [hb1l, hi2]; omega))
    intro b2 hb2
    rw [hb2, hb1, hi2, pgs_post, List.append_assoc]


private theorem any_tagged_false (sids : Slice binlog.events.previous_gtids_event.PreviousGtidsSid) (hn : ∀ s ∈ sids.val, s.tag = none) (k : Nat) :
    ∀ (i : Usize), sids.length - i.val = k → binlog.events.previous_gtids_event.any_tagged sids i ⦃ b => b = false ⦄ := by
  induction k with
  | zero =>
    intro i hk
    unfold binlog.events.previous_gtids_event.any_tagged
    simp only [Slice.length] at hk
    step*
  | succ k ih =>
    intro i hk
    unfold binlog.events.previous_gtids_event.any_tagged
    have hlt : i.val < sids.val.length := by simp only [Slice.length] at hk; omega
    step*
    have := hn _ (List.getElem_mem hlt); simp_all

private theorem serialize_body (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none)
    (buf : alloc.vec.Vec U8) (h : buf.length + (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ pgEnc e ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize binlog.events.previous_gtids_event.PreviousGtidsEvent.is_tagged
  step with any_tagged_false (alloc.vec.Vec.deref e.sids) (by simpa [alloc.vec.Vec.deref] using hn) _ 0#usize rfl as ⟨b, hb⟩
  subst hb
  simp only [binlog.events.previous_gtids_event.header_of_n_sids, Bool.false_eq_true, ↓reduceIte]
  have hpl : (pgEnc e).length = 8 + ((e.sids.val.map pgSidEnc).flatten).length := by
    simp [pgEnc, length_leBytes]
  step*
  have hl1 : buf1.length = buf.length + 8 := by
    simp [alloc.vec.Vec.length, buf1_post, s_post, a_post, length_leBytes]
  have hd : (alloc.vec.Vec.deref e.sids).val = e.sids.val := by simp [alloc.vec.Vec.deref]
  have := serialize_sids_spec (alloc.vec.Vec.deref e.sids) _ 0#usize buf1 rfl (by simp) (by
    rw [hl1, hd]; simp only [UScalar.ofNatCore_val_eq, List.drop_zero]
    simp only [alloc.vec.Vec.length] at h ⊢; omega)
  apply WP.spec_mono this
  intro b hb
  have hh : header.val = e.sids.length := by simp [header_post]
  simp only [hb, buf1_post, s_post, a_post, hh, pgEnc, List.append_assoc]
  simp [alloc.vec.Vec.deref]

/-- `sids`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids e ⦃ s => s.val = e.sids.val ⦄ := by
  simp [binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids, alloc.vec.Vec.deref]

/-- `into_owned` of an event without tags: the same SIDs. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned e ⦃ e' => e'.sids.val.map pgSidView = e.sids.val.map pgSidView ∧ ∀ s ∈ e'.sids.val, s.tag = none ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned
  step with sids_into_owned_none e.sids.val.length e.sids rfl hn as ⟨v, hv⟩
  simp only [hv]
  exact ⟨trivial, hn⟩

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize` in the untagged format (byte 7 of the count is 0): total; `pgRead`; no SID has a tag. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (hu : ∀ b, buf.val[7]? = some b → b.val = 0) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) => e.sids.val.map pgSidView) (pgRead buf.val) r rest ∧
      ∀ e, okPart r = some e → ∀ s ∈ e.sids.val, s.tag = none ⦄ := by
  sorry

/-- `MyDeserialize` on fewer than 8 bytes: an error. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_short (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 8) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  simp [okPart]

/-- `MySerialize` of an event without tags: the untagged format (`pgEnc`). -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (buf : alloc.vec.Vec U8) (h : buf.length + (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ pgEnc e ⦄ := by
  exact serialize_body e hn buf h

/-- Round trip, for an event without tags and fewer than `2^56` SIDs. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (hl : e.sids.length < 2 ^ 56) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = pgEnc e ++ tail) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.previous_gtids_event.PreviousGtidsEvent) => x.sids.val.map pgSidView) = some (e.sids.val.map pgSidView) ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogStruct::len` of an event without tags: the length of `pgEnc`, capped. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (v : binlog.consts.BinlogVersion) (h : (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (pgEnc e).length evLenCap ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  step with serialize_body e hn (alloc.vec.Vec.new U8) (by simpa [alloc.vec.Vec.new, alloc.vec.Vec.length] using h) as ⟨t, ht⟩
  step*
  · rw [i1_post]; simp [BinlogEvGtid.header_len_val]
  · have hh := BinlogEvGtid.header_len_val
    have ht' : t.val.length = (pgEnc e).length := by rw [ht]; simp [alloc.vec.Vec.new]
    simp only [n_post, i2_post, i1_post, hh, alloc.vec.Vec.len_val, evLenCap]
    simp [ht']

/-- `BinlogEvent::EVENT_TYPE`: `PREVIOUS_GTIDS_EVENT` (35). -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .PREVIOUS_GTIDS_EVENT := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
