import Defs
import Proofs.Util.BinlogEvGtid
import Proofs.Packets.GnoInterval

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

/-! ### Deserialization helpers -/

private theorem gno_size : packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 16#usize := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

private theorem parse_gno (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.parse packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      (okPart r).map (fun g => (g.start.1.val, g.«end».1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧ rest.val = buf.val.drop 16 ⦄ := by
  have := io.ParseBuf.parse_of_size packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () 16#usize
    (by simp [gno_size]) h
    (fun o => o.map (fun g : packets.GnoInterval => (g.start.1.val, g.«end».1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)))
    (fun sub hsub => by
      apply WP.spec_mono (packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec sub
        (by simp only [Slice.length, hsub, List.length_take, UScalar.ofNatCore_val_eq] at h ⊢; omega))
      rintro ⟨r, rest⟩ ⟨hr, _⟩
      simpa [hsub, List.take_take, List.drop_take, UScalar.ofNatCore_val_eq] using hr)
  exact this

private theorem parse_gno_short (buf : io.ParseBuf) (h : buf.length < 16) :
    io.ParseBuf.parse packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r _ => okPart r = none ⦄ := by
  apply WP.spec_mono (io.ParseBuf.parse_of_size_short _ buf () 16#usize (by simp [gno_size]) (by simp only [UScalar.ofNatCore_val_eq]; omega))
  rintro ⟨r, rest⟩ ⟨hr, _⟩
  exact hr

private theorem parse_intervals_spec (k : Nat) : ∀ (buf : io.ParseBuf) (n : U64) (ints : alloc.vec.Vec packets.GnoInterval),
    n.val = k → ints.length + buf.length ≤ Usize.max →
    binlog.events.previous_gtids_event.parse_intervals buf n ints ⦃ r rest ints' =>
      match pgIntervalsRead k buf.val with
      | some (is, t) => okPart r = some () ∧ rest.val = t ∧
          ints'.val.map (fun g : packets.GnoInterval => (g.start.1.val, g.«end».1.val)) =
            ints.val.map (fun g : packets.GnoInterval => (g.start.1.val, g.«end».1.val)) ++ is
      | none => okPart r = none ⦄ := by
  induction k with
  | zero =>
    intro buf n ints hn _
    unfold binlog.events.previous_gtids_event.parse_intervals
    have : n = 0#u64 := by scalar_tac
    simp [this, pgIntervalsRead, okPart]
  | succ k ih =>
    intro buf n ints hn hb
    unfold binlog.events.previous_gtids_event.parse_intervals
    have : n ≠ 0#u64 := by intro h; subst h; simp at hn
    simp only [this, ↓reduceIte, pgIntervalsRead]
    by_cases h16 : 16 ≤ buf.length
    · step with parse_gno buf h16 as ⟨r, b1, hr, hb1⟩
      cases r with
      | Err e => simp [okPart] at hr
      | Ok g =>
      simp only [okPart, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      have hl : ints.length < Usize.max := by simp only [Slice.length] at h16 hb; omega
      simp only [core.result.Result.Insts.CoreOpsTry.branch, h16, ↓reduceIte]
      step*
      · simp only [alloc.vec.Vec.length, intervals1_post, List.length_append, List.length_singleton, Slice.length, hb1,
          List.length_drop] at hb h16 ⊢; omega
      · rw [hb1] at r_post
        cases hp : pgIntervalsRead k (List.drop 16 buf.val) with
        | none => simp_all
        | some p =>
          obtain ⟨is, t⟩ := p
          simp_all
    · step with parse_gno_short buf (by omega) as ⟨r, b1, hr⟩
      cases r with
      | Ok g => simp [okPart] at hr
      | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, h16, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]

private theorem parse_sid_spec (buf : io.ParseBuf) :
    binlog.events.previous_gtids_event.parse_sid buf false ⦃ r rest =>
      if buf.val.length < 24 then okPart r = none else
      match pgIntervalsRead (leNat ((buf.val.drop 16).take 8)) (buf.val.drop 24) with
      | none => okPart r = none
      | some (is, t) => (okPart r).map pgSidView = some (buf.val.take 16, is) ∧ rest.val = t ∧
          ∀ s, okPart r = some s → s.tag = none ⦄ := by
  unfold binlog.events.previous_gtids_event.parse_sid binlog.events.previous_gtids_event.parse_sid_tag
  simp only [Bool.false_eq_true, ↓reduceIte]
  step*
  · have : buf.val.length < 24 := by scalar_tac
    simp [okPart, this]
  · have : buf.val.length < 24 := by scalar_tac
    simp [okPart, this]
  · have h24 : ¬ buf.val.length < 24 := by scalar_tac
    have hs3 : s3.val.length ≥ 8 := by scalar_tac
    have hn : n_intervals.val = leNat ((buf.val.drop 16).take 8) := by
      have : n_intervals.val = n_intervals.bv.toNat := rfl
      rw [this, n_intervals_post, PBUtil.fromLEBytes_cast_toNat, to_slice_mut_back1_post,
        Array.from_slice_val _ _ (by simp [s6_post, s5_post1]), s6_post, s5_post, s3_post]
      simp [List.slice]
    have hs7 : s7.val = buf.val.drop 24 := by simp [s7_post, s3_post]
    step with parse_intervals_spec _ s7 n_intervals (alloc.vec.Vec.with_capacity packets.GnoInterval i2) rfl
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length]) as ⟨r1, buf2, ints1, hp⟩
    simp only [h24, ↓reduceIte, ← hn, ← hs7]
    have hval : val = none := by simp_all
    have hu : (to_slice_mut_back s2).val = buf.val.take 16 := by
      rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by simp [s2_post, s1_post1]), s2_post, s1_post]
      simp [List.slice]
    cases hq : pgIntervalsRead n_intervals.val s7.val with
    | none =>
      rw [hq] at hp
      cases r1 with
      | Ok _ => simp [okPart] at hp
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
    | some p =>
      obtain ⟨is, t⟩ := p
      rw [hq] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      cases r1 with
      | Err _ => simp [okPart] at h1
      | Ok _ =>
        simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, pgSidView, hu, h2, hval, h3,
          alloc.vec.Vec.with_capacity]

private theorem pgIntervalsRead_length (n : Nat) : ∀ (bs : List U8) (is : List (Nat × Nat)) (t : List U8),
    pgIntervalsRead n bs = some (is, t) → t.length ≤ bs.length := by
  induction n with
  | zero => intro bs is t h; simp [pgIntervalsRead] at h; rw [h.2]
  | succ n ih =>
    intro bs is t h
    simp only [pgIntervalsRead] at h
    split_ifs at h with h16
    cases hq : pgIntervalsRead n (bs.drop 16) with
    | none => simp [hq] at h
    | some p =>
      obtain ⟨is', t'⟩ := p
      simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      have := ih _ _ _ hq
      rw [← h.2]; simp at this; omega

private theorem parse_sids_spec (k : Nat) : ∀ (buf : io.ParseBuf) (n : U64) (sids : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid),
    n.val = k → sids.length + buf.length ≤ Usize.max → (∀ s ∈ sids.val, s.tag = none) →
    binlog.events.previous_gtids_event.parse_sids buf false n sids ⦃ r rest sids' =>
      match pgSidsRead k buf.val with
      | some (ss, t) => okPart r = some () ∧ rest.val = t ∧
          sids'.val.map pgSidView = sids.val.map pgSidView ++ ss ∧ ∀ s ∈ sids'.val, s.tag = none
      | none => okPart r = none ⦄ := by
  induction k with
  | zero =>
    intro buf n sids hn _ hs
    unfold binlog.events.previous_gtids_event.parse_sids
    have : n = 0#u64 := by scalar_tac
    simpa [this, pgSidsRead, okPart] using hs
  | succ k ih =>
    intro buf n sids hn hb hs
    unfold binlog.events.previous_gtids_event.parse_sids
    have : n ≠ 0#u64 := by intro h; subst h; simp at hn
    simp only [this, ↓reduceIte, pgSidsRead]
    step with parse_sid_spec buf as ⟨r, b1, hr⟩
    by_cases h24 : buf.val.length < 24
    · simp only [h24, ↓reduceIte] at hr ⊢
      cases r with
      | Ok _ => simp [okPart] at hr
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
    · simp only [h24, ↓reduceIte] at hr ⊢
      cases hq : pgIntervalsRead (leNat ((buf.val.drop 16).take 8)) (buf.val.drop 24) with
      | none =>
        rw [hq] at hr
        cases r with
        | Ok _ => simp [okPart] at hr
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
      | some p =>
        obtain ⟨is, t⟩ := p
        rw [hq] at hr
        obtain ⟨h1, h2, h3⟩ := hr
        cases r with
        | Err _ => simp [okPart] at h1
        | Ok x =>
        simp only [okPart, Option.map_some, Option.some.injEq] at h1 h3
        have hx : x.tag = none := h3 x rfl
        have htl := pgIntervalsRead_length _ _ _ _ hq
        simp only [List.length_drop] at htl
        have hl : sids.length < Usize.max := by simp only [Slice.length] at hb; omega
        simp only [core.result.Result.Insts.CoreOpsTry.branch]
        step*
        · simp only [alloc.vec.Vec.length, sids1_post, List.length_append, List.length_singleton, Slice.length, h2] at hb ⊢
          omega
        · intro s hs'; rw [sids1_post] at hs'; simp at hs'; rcases hs' with hs' | hs'
          · exact hs s hs'
          · rw [hs']; exact hx
        · rw [h2] at r_post
          cases hp : pgSidsRead k t with
          | none => simp_all
          | some p =>
            obtain ⟨ss, t'⟩ := p
            simp_all

private theorem n_sids_untagged (h : U64) :
    binlog.events.previous_gtids_event.n_sids_of_header h false ⦃ n => n.val = h.val % 2 ^ 56 ⦄ := by
  unfold binlog.events.previous_gtids_event.n_sids_of_header
  simp only [Bool.false_eq_true, ↓reduceIte]
  step*
  have hi : i.val = 2 ^ 56 := by rw [i_post]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  rw [UScalar.val_and, i1_post, hi, Nat.and_two_pow_sub_one_eq_mod]

private theorem leNat_take8_lt (bs : List U8) (h8 : 8 ≤ bs.length) (hu : ∀ b, bs[7]? = some b → b.val = 0) :
    leNat (bs.take 8) < 2 ^ 56 := by
  have h7 : bs[7]? = some bs[7] := List.getElem?_eq_getElem (by omega)
  have hb : bs[7] = 0#u8 := UScalar.eq_of_val_eq (by simpa using hu _ h7)
  rw [List.take_add_one, h7, hb]
  have := leNat_append_zeros (bs.take 7) 1
  simp only [List.replicate_one] at this
  simp only [Option.toList_some, this]
  have := leNat_lt (bs.take 7)
  simpa [List.length_take, show min 7 bs.length = 7 by omega] using this

private theorem pgIntervalsRead_enc (l : List packets.GnoInterval) (t : List U8) :
    pgIntervalsRead l.length ((l.map gnoIntervalEnc).flatten ++ t) =
      some (l.map (fun g : packets.GnoInterval => (g.start.1.val, g.«end».1.val)), t) := by
  induction l with
  | nil => simp [pgIntervalsRead]
  | cons g l ih =>
    have h16 : 16 ≤ (gnoIntervalEnc g ++ ((l.map gnoIntervalEnc).flatten ++ t)).length := by
      simp [gnoIntervalEnc, length_leBytes]; omega
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, pgIntervalsRead, h16, ↓reduceIte]
    have hd : (gnoIntervalEnc g ++ ((l.map gnoIntervalEnc).flatten ++ t)).drop 16 = (l.map gnoIntervalEnc).flatten ++ t := by
      simp [gnoIntervalEnc, List.drop_append, length_leBytes]
    rw [hd, ih]
    simp [gnoIntervalEnc, BinlogEvGtid.leNat_leBytes_u64]

private theorem pgSidsRead_enc (l : List binlog.events.previous_gtids_event.PreviousGtidsSid) (t : List U8) :
    pgSidsRead l.length ((l.map pgSidEnc).flatten ++ t) = some (l.map pgSidView, t) := by
  induction l with
  | nil => simp [pgSidsRead]
  | cons x l ih =>
    have hu : x.uuid.val.length = 16 := by simp
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, pgSidsRead]
    generalize (l.map pgSidEnc).flatten ++ t = A at ih ⊢
    have hn : x.intervals.length < 2 ^ 64 := by
      have h1 := x.intervals.property
      have h2 : Usize.max < 2 ^ 64 := by
        rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]
      simp only [alloc.vec.Vec.length]; omega
    have e : pgSidEnc x ++ A = x.uuid.val ++ (leBytes 8 x.intervals.length ++ ((x.intervals.val.map gnoIntervalEnc).flatten ++ A)) := by
      simp [pgSidEnc]
    have h24 : ¬ (pgSidEnc x ++ A).length < 24 := by
      rw [List.length_append, pgSidEnc_length]; omega
    have ht : (pgSidEnc x ++ A).take 16 = x.uuid.val := by rw [e, List.take_left' hu]
    have hd : (pgSidEnc x ++ A).drop 16 = leBytes 8 x.intervals.length ++ ((x.intervals.val.map gnoIntervalEnc).flatten ++ A) := by
      rw [e, List.drop_left' hu]
    have hd24 : (pgSidEnc x ++ A).drop 24 = (x.intervals.val.map gnoIntervalEnc).flatten ++ A := by
      rw [show 24 = 16 + 8 by rfl, ← List.drop_drop, hd, BinlogEvGtid.drop_leBytes_append]
    simp only [h24, ↓reduceIte]
    rw [hd, BinlogEvGtid.take_leBytes_append, BinlogEvGtid.leNat_leBytes_lt _ _ hn, hd24, ht]
    have := pgIntervalsRead_enc x.intervals.val A
    simp only [alloc.vec.Vec.length] at this ⊢
    rw [this]
    simp [ih, pgSidView]

private theorem leBytes8_byte7 (n : Nat) (hn : n < 2 ^ 56) (X : List U8) :
    ∀ b, (leBytes 8 n ++ X)[7]? = some b → b.val = 0 := by
  intro b hb
  simp only [leBytes, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hb
  rw [← hb, PBUtil.byte_val]
  simp only [Nat.div_div_eq_div_mul]
  rw [Nat.div_eq_of_lt (by omega)]

private theorem pgRead_enc (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hl : e.sids.length < 2 ^ 56) (tail : List U8) :
    pgRead (pgEnc e ++ tail) = some (e.sids.val.map pgSidView, tail) := by
  have h8 : ¬ (pgEnc e ++ tail).length < 8 := by simp [pgEnc, length_leBytes]
  unfold pgRead
  simp only [h8, ↓reduceIte]
  simp only [pgEnc, List.append_assoc, BinlogEvGtid.take_leBytes_append, BinlogEvGtid.drop_leBytes_append,
    BinlogEvGtid.leNat_leBytes_lt _ _ (show e.sids.length < 2 ^ (8 * 8) by omega), Nat.mod_eq_of_lt hl]
  exact pgSidsRead_enc e.sids.val tail

/-- `MyDeserialize` in the untagged format (byte 7 of the count is 0): total; `pgRead`; no SID has a tag. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (hu : ∀ b, buf.val[7]? = some b → b.val = 0) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) => e.sids.val.map pgSidView) (pgRead buf.val) r rest ∧
      ∀ e, okPart r = some e → ∀ s ∈ e.sids.val, s.tag = none ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  · have : buf.val.length < 8 := by scalar_tac
    simp [ReadsAs, pgRead, this, okPart]
  · have h8 : ¬ buf.val.length < 8 := by scalar_tac
    have hh : header.val = leNat (buf.val.take 8) := by
      have : header.val = header.bv.toNat := rfl
      rw [this, header_post, PBUtil.fromLEBytes_cast_toNat, to_slice_mut_back_post,
        Array.from_slice_val _ _ (by simp [s2_post, s1_post1]), s2_post, s1_post]
      simp [List.slice]
    have hlt := leNat_take8_lt buf.val (by omega) hu
    have hf : (format != 0#u8) = false := by
      have : format.val = 0 := by
        rw [format_post, UScalar.cast_val_eq, i1_post, hh, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
        simp
      simp only [bne_eq_false_iff_eq]; exact UScalar.eq_of_val_eq (by simpa using this)
    simp only [hf]
    step with n_sids_untagged header as ⟨n_sids, hn⟩
    have hd8 : List.drop 8 buf.val = s3.val := s3_post.symm
    step as ⟨i2, _⟩
    step with parse_sids_spec _ s3 n_sids (alloc.vec.Vec.with_capacity binlog.events.previous_gtids_event.PreviousGtidsSid i2) rfl
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length]) (by simp [alloc.vec.Vec.with_capacity]) as ⟨r, b1, sids1, hp⟩
    simp only [ReadsAs, pgRead, h8, ↓reduceIte, ← hh, ← hn, hd8]
    cases hq : pgSidsRead n_sids.val s3.val with
    | none =>
      rw [hq] at hp
      cases r with
      | Ok _ => simp [okPart] at hp
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
    | some p =>
      obtain ⟨ss, t⟩ := p
      rw [hq] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hp
      cases r with
      | Err _ => simp [okPart] at h1
      | Ok _ =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch, okPart, h2, h3, alloc.vec.Vec.with_capacity] using h4

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
  -- `hn` is not needed: the untagged reader never reads a tag, whatever the event's tags are.
  have _ := hn
  have hu : ∀ b, buf.val[7]? = some b → b.val = 0 := by
    rw [h, pgEnc, List.append_assoc]; exact leBytes8_byte7 _ hl _
  apply WP.spec_mono (binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf hu)
  rintro ⟨r, rest⟩ ⟨hr, _⟩
  rw [h, pgRead_enc e hl tail] at hr
  exact hr

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
