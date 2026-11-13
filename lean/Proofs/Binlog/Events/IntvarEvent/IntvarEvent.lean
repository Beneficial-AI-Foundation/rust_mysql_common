import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct IntvarEvent and its impls` (spec file: `Specs/Binlog/Events/IntvarEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(subtype, value)`: those fields. -/
theorem binlog.events.intvar_event.IntvarEvent.new_spec (t : binlog.consts.IntvarEventType) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.new t value ⦃ e => e.subtype.1 = t ∧ e.value.1 = value ⦄ := by
  unfold binlog.events.intvar_event.IntvarEvent.new
  step*

/-- `subtype`: the subtype. -/
theorem binlog.events.intvar_event.IntvarEvent.impl.subtype_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.subtype e = ok e.subtype.1 := by
  obtain ⟨⟨t, u⟩, v⟩ := e; rfl

/-- `value`: the value. -/
theorem binlog.events.intvar_event.IntvarEvent.impl.value_eq (e : binlog.events.intvar_event.IntvarEvent) :
    binlog.events.intvar_event.IntvarEvent.impl.value e = ok e.value.1 := by
  obtain ⟨t, ⟨v, u⟩⟩ := e; rfl

/-- `with_subtype`: replaces the subtype. -/
theorem binlog.events.intvar_event.IntvarEvent.with_subtype_spec (e : binlog.events.intvar_event.IntvarEvent) (t : binlog.consts.IntvarEventType) :
    binlog.events.intvar_event.IntvarEvent.with_subtype e t ⦃ e' => e'.subtype.1 = t ∧ e'.value = e.value ⦄ := by
  unfold binlog.events.intvar_event.IntvarEvent.with_subtype
  step*

/-- `with_value`: replaces the value. -/
theorem binlog.events.intvar_event.IntvarEvent.with_value_spec (e : binlog.events.intvar_event.IntvarEvent) (value : U64) :
    binlog.events.intvar_event.IntvarEvent.with_value e value ⦃ e' => e'.subtype = e.subtype ∧ e'.value.1 = value ⦄ := by
  unfold binlog.events.intvar_event.IntvarEvent.with_value
  step*

/-- `MyDeserialize::SIZE` is `some 9#usize`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = some 9#usize := by
  unfold binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize` on at least 9 bytes: `intvarRead` (an unknown subtype is an error). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : 9 ≤ buf.length) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄ := by
  unfold binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  all_goals
    obtain ⟨b, l, hbl⟩ := BinlogEvGtid.list_cons_of_length_pos buf.val (by simp [Slice.length] at h; omega)
    have hr := r_post1 b (by simp [hbl])
    have hl9 : ¬ (l.length + 1 < 9) := by
      have : (b :: l).length ≥ 9 := by rw [← hbl]; simpa [Slice.length] using h
      simp at this; omega
    simp only [ReadsAs, intvarRead, hbl, List.length_cons, hl9, ite_false] at *
    cases ht : intvarTypeOfCode b.val <;> simp only [ht] at hr <;> obtain ⟨_, rfl, _⟩ := hr <;>
      simp_all [okPart]

/-- `MyDeserialize` panics on fewer than 9 bytes, unless the first byte is an unknown subtype (then it is an error). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_panics (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 9)
    (hs : ∀ b, buf.val.head? = some b → intvarTypeOfCode b.val ≠ none) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = fail .panic := by
  unfold binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  by_cases h0 : buf.length < 1
  · exact bind_fail_left (BinlogEvGtid.parse_unchecked_intvar_type_panics buf h0)
  · apply bind_fail_of_spec (BinlogEvGtid.parse_unchecked_intvar_type buf (by omega))
    rintro ⟨r, buf1⟩ ⟨hb1, hr⟩
    obtain ⟨b, l, hbl⟩ := BinlogEvGtid.list_cons_of_length_pos buf.val (by simp only [Slice.length] at h0; omega)
    have hr' := hr b (by simp [hbl])
    have hk := hs b (by simp [hbl])
    cases ht : intvarTypeOfCode b.val with
    | none => exact absurd ht hk
    | some t =>
      simp only [ht] at hr'
      obtain ⟨x, rfl, -⟩ := hr'
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      have : buf1.length < 8 := by
        simp only [Slice.length, hb1, List.length_drop]; simp only [Slice.length] at h; omega
      exact bind_fail_left (BinlogEvGtid.rawint_leu64_parse_unchecked_panics buf1 this)

/-- `buf.parse::<IntvarEvent>(ctx)`: total (`SIZE` checked first); `intvarRead`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_parse_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    io.ParseBuf.parse binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx buf ctx ⦃ r rest => ReadsAs (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) (intvarRead buf.val) r rest ⦄ := by
  have hs : proto.MyDeserialize.SIZE binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx = ok (some 9#usize) := by
    simp only [binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq]
  have hfst : ∀ bs : List U8, 9 ≤ bs.length → (intvarRead (bs.take 9)).map Prod.fst = (intvarRead bs).map Prod.fst := by
    intro bs hb
    obtain ⟨b, l, rfl⟩ := BinlogEvGtid.list_cons_of_length_pos bs (by omega)
    simp only [List.length_cons] at hb
    simp only [intvarRead, List.take_succ_cons, List.length_cons, List.length_take, List.head?_cons,
      Option.bind_some, List.drop_succ_cons, List.drop_zero, List.take_take]
    split_ifs <;> try omega
    cases intvarTypeOfCode b.val <;> simp
  by_cases hl : 9 ≤ buf.length
  · have := io.ParseBuf.parse_of_size _ buf ctx 9#usize hs hl
      (fun o => o.map (fun (x : binlog.events.intvar_event.IntvarEvent) => (x.subtype.1, x.value.1.val)) =
        (intvarRead buf.val).map Prod.fst)
    apply WP.spec_mono (this ?_)
    · rintro ⟨r, rest⟩ ⟨h1, h2⟩
      apply BinlogEvGtid.readsAs_of _ _ _ _ h1
      intro v t ht
      rw [h2]
      revert ht
      obtain ⟨b, l, hbl⟩ := BinlogEvGtid.list_cons_of_length_pos buf.val (by simp [Slice.length] at hl; omega)
      rw [hbl]
      simp only [intvarRead]
      split_ifs
      · simp
      · split <;> simp_all
    · intro sub hsub
      have hsl : 9 ≤ sub.length := by simp [Slice.length, hsub]; scalar_tac
      apply WP.spec_mono (deserialize_spec ctx sub hsl)
      rintro ⟨r, rest⟩ h1
      simp only [WP.uncurry']
      rw [BinlogEvGtid.readsAs_fst _ _ _ _ h1, hsub]
      exact hfst _ (by simpa [Slice.length] using hl)
  · have hn : intvarRead buf.val = none := by
      simp [intvarRead, show buf.val.length < 9 by simpa [Slice.length] using hl]
    rw [hn]
    apply WP.spec_mono (io.ParseBuf.parse_of_size_short _ buf ctx 9#usize hs (by scalar_tac))
    rintro ⟨r, rest⟩ ⟨h1, -⟩
    exact h1

/-- `MySerialize`: appends the layout `intvarEnc`. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.intvar_event.IntvarEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (intvarEnc e).length ≤ Usize.max) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ intvarEnc e ⦄ := by
  unfold binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [intvarEnc, List.length_cons, length_leBytes] at h
  step*
  · have : buf1.length = buf.length + 1 := by simp [alloc.vec.Vec.length, buf1_post]
    omega
  · simp_all [intvarEnc]

/-- Round trip. -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.intvar_event.IntvarEvent) (ctx : binlog.BinlogCtx) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = intvarEnc e ++ tail) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄ := by
  have hl : 9 ≤ buf.length := by simp [Slice.length, h, intvarEnc, length_leBytes]
  apply WP.spec_mono (deserialize_spec ctx buf hl)
  rintro ⟨r, rest⟩ hr
  have hs : intvarRead buf.val = some ((e.subtype.1, e.value.1.val), tail) := by
    have hc : (byte (intvarTypeCode e.subtype.1)).val = intvarTypeCode e.subtype.1 := by
      rw [byte_val]; exact Nat.mod_eq_of_lt (by have := BinlogEvGtid.intvarTypeCode_lt e.subtype.1; omega)
    simp [intvarRead, h, intvarEnc, length_leBytes, hc, BinlogEvGtid.intvarTypeOfCode_code,
      BinlogEvGtid.leNat_leBytes_u64]
  rw [hs] at hr
  obtain ⟨hm, hrest⟩ := hr
  obtain ⟨x, rfl, hx⟩ := BinlogEvGtid.okPart_map_eq_some hm
  refine ⟨?_, hrest⟩
  obtain ⟨⟨t1, u1⟩, ⟨v1, w1⟩⟩ := x
  obtain ⟨⟨t2, u2⟩, ⟨v2, w2⟩⟩ := e
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, hv⟩ := hx
  have := UScalar.eq_of_val_eq hv
  subst this
  rfl

/-- `BinlogEvent::EVENT_TYPE`: `INTVAR_EVENT` (5). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INTVAR_EVENT := by
  unfold binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: 9 (= the length of `intvarEnc`). -/
theorem binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.intvar_event.IntvarEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 9#usize := by
  rfl

end mysql_common
