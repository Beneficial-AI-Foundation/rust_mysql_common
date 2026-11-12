import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Value.Value
import Proofs.Constants.CursorType
import Proofs.Constants.StmtExecuteParamsFlags
import Proofs.Constants.StmtExecuteParamFlags

/-! Statements for `struct ComStmtExecuteRequest and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

/-- `stmt_id`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.stmt_id self = ok self.stmt_id.1 := by
  rfl

/-- `flags`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.flags self = ok self.flags.1 := by
  rfl

/-- `bitmap`: the bitmap bytes, at most 8192 (`BareBytes<8192>`). -/
theorem packets.ComStmtExecuteRequest.impl.bitmap_spec (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.bitmap self ⦃ s => s.val = (cowList self.bitmap.1).take 8192 ⦄ := by
  unfold packets.ComStmtExecuteRequest.impl.bitmap
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ 8192#usize
    (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) self.bitmap)
  intro s hs; rw [hs]; rfl

/-- `params_flags`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.params_flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params_flags self = ok self.params_flags.1 := by
  rfl

/-- `params`: the parameters (a slice of values: patch 28). -/
theorem packets.ComStmtExecuteRequest.impl.params_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params self = ok self.params := by
  rfl

/-- `as_long_data`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.as_long_data_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.as_long_data self = ok self.as_long_data := by
  rfl

private theorem cast_disc (ct : constants.ColumnType) :
    UScalar.cast .U8 (read_discriminant ct) = byte (columnTypeCode ct) := by
  obtain ⟨p, hp, hpv⟩ := mysql_common.PBUtil.spec_eq_ok (U8.Insts.CoreConvertFromColumnType.from_spec ct)
  have : U8.Insts.CoreConvertFromColumnType.from ct = ok (UScalar.cast .U8 (read_discriminant ct)) := rfl
  rw [this] at hp
  simp only [ok.injEq] at hp
  rw [hp]
  exact byte_eq_of_val _ _ hpv

private theorem flatten_take_succ {α β : Type} (f : α → List β) (l : List α) (k : Nat) (hk : k < l.length) :
    ((l.take (k + 1)).map f).flatten = ((l.take k).map f).flatten ++ f (l[k]'hk) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.map_append, List.flatten_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil]

private theorem flatten_take_length_le {α β : Type} (f : α → List β) (l : List α) (k : Nat) :
    ((l.take k).map f).flatten.length ≤ (l.map f).flatten.length := by
  have := congrArg (fun l => (l.map f).flatten.length) (List.take_append_drop k l)
  simp only [List.map_append, List.flatten_append, List.length_append] at this
  omega

private theorem loop0_spec (params : Slice value.Value) (k : Usize) (buf0 buf : alloc.vec.Vec U8)
    (hk : k.val ≤ params.length)
    (hbuf : buf.val = buf0.val ++ ((params.val.take k.val).map (fun v => paramType (Val.ofValue v))).flatten)
    (hmax : buf0.length + ((params.val.map (fun v => paramType (Val.ofValue v))).flatten).length ≤ Usize.max) :
    packets.serialize_params_loop0 { start := k, «end» := Slice.len params } params buf ⦃ b =>
      b.val = buf0.val ++ ((params.val.map (fun v => paramType (Val.ofValue v))).flatten) ⦄ := by
  unfold packets.serialize_params_loop0
  apply loop.spec_decr_nat (fun p => params.length - p.1.start.val)
    (fun p => p.1.end = Slice.len params ∧ p.1.start.val ≤ params.length ∧
      p.2.val = buf0.val ++ ((params.val.take p.1.start.val).map (fun v => paramType (Val.ofValue v))).flatten)
  · rintro ⟨it, b⟩ ⟨h1, h2, h3⟩
    unfold packets.serialize_params_loop0.body
    step*
    · have h1' : it.end = Slice.len params := h1
      have hend : it.end.val = params.length := by rw [h1']; simp [Slice.len]
      have hc : ¬ it.start.val < it.end.val := by
        intro hc; simp only [hc, ite_true] at o_post; simp_all
      have heq : it.start.val = params.val.length := by simp only [Slice.length] at hend h2; omega
      simp only at h3
      rw [h3, heq, List.take_length]
    · have h1' : it.end = Slice.len params := h1
      have hend : it.end.val = params.length := by rw [h1']; simp [Slice.len]
      split_ifs at o_post with hc
      · simp_all
      · simp_all
    · cases param <;>
        simp only [constants.StmtExecuteParamFlags.empty, constants.StmtExecuteParamFlags.bits,
          Aeneas.Std.bind_ok, Aeneas.Std.bind_tc_ok] <;>
        step*
      all_goals
        have hc : it.start.val < it.end.val := by
          by_contra hc; simp only [hc, ite_false] at o_post; simp_all
        have hi : i = it.start := by
          have o_post' := o_post
          simp only [hc, ite_true] at o_post'
          obtain ⟨ho, -⟩ := o_post'
          subst ho; exact (Option.some.inj ‹_›).symm
        subst hi
        have hlen : it.start.val < params.val.length := by
          have h1' : it.end = Slice.len params := h1
          have : it.end.val = params.length := by rw [h1']; simp [Slice.len]
          simp only [Slice.length] at this; omega
        have hsucc := flatten_take_succ (fun v => paramType (Val.ofValue v)) params.val it.start.val hlen
        simp only [← param_post] at hsucc
        have hle := flatten_take_length_le (fun v => paramType (Val.ofValue v)) params.val (it.start.val + 1)
        simp only [hsucc, List.length_append] at hle
        have hs_len : s.length = 2 := by rw [s_post]; rfl
        simp only [s_post, i1_post, cast_disc] at *
        simp only [paramType.eq_1, paramType.eq_2, paramType.eq_3, paramType.eq_4, paramType.eq_5, paramType.eq_6, paramType.eq_7, paramType.eq_8, Val.ofValue.eq_1, Val.ofValue.eq_2, Val.ofValue.eq_3, Val.ofValue.eq_4, Val.ofValue.eq_5, Val.ofValue.eq_6, Val.ofValue.eq_7, Val.ofValue.eq_8, List.length_cons, List.length_nil] at hsucc hle
        have h3' : b.val = buf0.val ++ ((params.val.take it.start.val).map (fun v => paramType (Val.ofValue v))).flatten := h3
        have hb_len : b.length = buf0.length + ((params.val.take it.start.val).map (fun v => paramType (Val.ofValue v))).flatten.length := by
          simp only [alloc.vec.Vec.length, h3', List.length_append]
        have hi1 : iter1.start.val = it.start.val + 1 := by
          simp only [hc, ite_true] at o_post; exact o_post.2
        have hb0 : byte 0 = 0#u8 := rfl
        have hb128 : byte 128 = constants.StmtExecuteParamFlags.UNSIGNED := by
          unfold constants.StmtExecuteParamFlags.UNSIGNED; rfl
        simp only [hb0, hb128] at hsucc
        first
        | omega
        | (have h1'' : it.end = Slice.len params := h1
           rw [hi1, hsucc]
           refine ⟨by rw [o_post1, h1''], by simp only [Slice.length]; omega, ?_, by simp only [Slice.length]; omega⟩
           simp_all)
  · exact ⟨rfl, hk, hbuf⟩

attribute [local step] value.Value.Insts.Mysql_commonProtoMySerialize.serialize_spec

private theorem loop1_spec (params : Slice value.Value) (ld : Bool) (k : Usize) (buf0 buf : alloc.vec.Vec U8)
    (hk : k.val ≤ params.length)
    (hbuf : buf.val = buf0.val ++ ((params.val.take k.val).map (fun v => paramValue ld (Val.ofValue v))).flatten)
    (hmax : buf0.length + ((params.val.map (fun v => paramValue ld (Val.ofValue v))).flatten).length ≤ Usize.max) :
    packets.serialize_params_loop1 { start := k, «end» := Slice.len params } params ld buf ⦃ b =>
      b.val = buf0.val ++ ((params.val.map (fun v => paramValue ld (Val.ofValue v))).flatten) ⦄ := by
  unfold packets.serialize_params_loop1
  apply loop.spec_decr_nat (fun p => params.length - p.1.start.val)
    (fun p => p.1.end = Slice.len params ∧ p.1.start.val ≤ params.length ∧
      p.2.val = buf0.val ++ ((params.val.take p.1.start.val).map (fun v => paramValue ld (Val.ofValue v))).flatten)
  · rintro ⟨it, b⟩ ⟨h1, h2, h3⟩
    have h1' : it.end = Slice.len params := h1
    have hend : it.end.val = params.length := by rw [h1']; simp [Slice.len]
    have h3' : b.val = buf0.val ++ ((params.val.take it.start.val).map (fun v => paramValue ld (Val.ofValue v))).flatten := h3
    unfold packets.serialize_params_loop1.body
    step*
    all_goals first
    | (have hc : ¬ it.start.val < it.end.val := by
          intro hc; simp only [hc, ite_true] at o_post; simp_all
       have heq : it.start.val = params.val.length := by simp only [Slice.length] at hend h2; omega
       rw [h3', heq, List.take_length]; done)
    | (split_ifs at o_post with hc <;> simp_all; done)
    | (have hc : it.start.val < it.end.val := by
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
       have hsucc := flatten_take_succ (fun v => paramValue ld (Val.ofValue v)) params.val it.start.val hlen
       have hle := flatten_take_length_le (fun v => paramValue ld (Val.ofValue v)) params.val (it.start.val + 1)
       have hb_len : b.length = buf0.length + ((params.val.take it.start.val).map (fun v => paramValue ld (Val.ofValue v))).flatten.length := by
         simp only [alloc.vec.Vec.length, h3', List.length_append]
       simp only [hsucc, List.length_append] at hle
       try subst param
       generalize hw : params.val[it.start.val]'hlen = w at *
       clear hw
       subst w
       cases ld <;>
       first
       | contradiction
       | (simp only [paramValue, Val.ofValue, Bool.false_eq_true, ↓reduceIte] at hle hmax hb_len ⊢; omega)
       | (have h1'' : it.end = Slice.len params := h1
          refine ⟨by rw [o_post1, h1''], by simp only [Slice.length]; omega, ?_, by simp only [Slice.length]; omega⟩
          rw [hi1, hsucc]
          first
          | (rw [‹buf1.val = _›, h3']; simp [paramValue, Val.ofValue])
          | (rw [h3']; simp [paramValue, Val.ofValue, binEnc])))
  · exact ⟨rfl, hk, hbuf⟩

@[step]
private theorem serialize_params_spec (params : Slice value.Value) (ld : Bool) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((params.val.map (fun v => paramType (Val.ofValue v))).flatten).length
      + ((params.val.map (fun v => paramValue ld (Val.ofValue v))).flatten).length ≤ Usize.max) :
    packets.serialize_params params ld buf ⦃ b =>
      b.val = buf.val ++ (params.val.map (fun v => paramType (Val.ofValue v))).flatten
        ++ (params.val.map (fun v => paramValue ld (Val.ofValue v))).flatten ⦄ := by
  unfold packets.serialize_params
  apply WP.spec_bind (loop0_spec params 0#usize buf buf (by simp) (by simp) (by omega))
  intro b1 hb1
  apply WP.spec_mono (loop1_spec params ld 0#usize b1 b1 (by simp) (by simp)
    (by simp only [alloc.vec.Vec.length, hb1, List.length_append] at h ⊢; omega))
  intro b2 hb2
  rw [hb2, hb1]

@[step]
private theorem const_cursor_serialize (x : misc.raw._const.Const constants.CursorType U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.CursorType.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromCursorType) U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ b => b.val = buf.val ++ [byte x.1.val] ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1
    (U8.Insts.CoreConvertFromCursorType.from_eq _), byte_eq_self]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

@[step]
private theorem const_pflags_serialize (x : misc.raw._const.Const constants.StmtExecuteParamsFlags U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize constants.StmtExecuteParamsFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromStmtExecuteParamsFlags) U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf
      ⦃ b => b.val = buf.val ++ [byte x.1.val] ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1
    (U8.Insts.CoreConvertFromStmtExecuteParamsFlags.from_eq _), byte_eq_self]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

@[step]
private theorem bitmap_serialize (rb : misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 8192#usize) Usize) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((cowList rb.1).take 8192).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 8192#usize) rb buf
      ⦃ b => b.val = buf.val ++ (cowList rb.1).take 8192 ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  rw [← hs] at h ⊢
  show misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize 8192#usize s buf ⦃ _ ⦄
  unfold misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize
  have key : ∀ (l : List U8) (m : Nat), List.take (min l.length m) l = List.take m l := by
    intro l m
    rcases le_total l.length m with h' | h'
    · rw [Nat.min_eq_left h', List.take_length, List.take_of_length_le h']
    · rw [Nat.min_eq_right h']
  simp only [core.cmp.min]
  step*
  all_goals simp_all [List.slice]

/-- `MySerialize for ComStmtExecuteRequest`: appends `stmtExecuteBytes` of its fields: header, statement id, flags, iteration count; if there are parameters, the bitmap (truncated to 8192 bytes), the params flags, the parameter types and the values (`Bytes` left out if `as_long_data`). -/
theorem packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComStmtExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
      self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data).length ≤ Usize.max) :
    packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
        self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data ⦄ := by
  simp only [stmtExecuteBytes, List.length_cons, List.length_append, mysql_common.PBUtil.length_leBytes] at h
  unfold packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize
  step*
  all_goals (simp_all [stmtExecuteBytes, alloc.vec.Vec.length, mysql_common.PBUtil.length_leBytes,
    Function.comp_def]; try omega)
  all_goals rfl

end mysql_common
