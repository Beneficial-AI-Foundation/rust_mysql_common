import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.RawBytesSeq
import Proofs.Misc.Raw.Bytes.NullBytes
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Int.LenEnc
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.LenencStrLen
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Util.PacketsColStmt
import Proofs.Io.BufMutExt
import Proofs.Defs.LemmasConn

/-! Helper lemmas for the connection-phase auth packets (`AuthMoreData`, `AuthPlugin`,
`AuthSwitchRequest`, `ComChangeUser`, `LocalInfilePacket`, ...). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common.CAUtil

/-- `buf.parse::<ConstU8<_, N>>(())`, by the first byte. -/
theorem header_parse_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) buf () ⦃ r rest =>
      match buf.val with
      | [] => okPart r = none ∧ rest = buf
      | b :: t => ((okPart r).isSome ↔ b.val = N.val) ∧ rest.val = t ⦄ := by
  apply WP.spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec N e d hd buf)
  rintro ⟨r, rest⟩ h
  cases hb : (↑buf : List U8) with
  | nil =>
    have hl : ¬ 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    simpa [hl] using h
  | cons b t =>
    have hl : 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    simp only [hl, ite_true, hb] at h
    simpa [leNat] using h

@[simp] theorem branch_ok {T E : Type} (x : T) :
    CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

@[simp] theorem branch_err {T E : Type} (x : E) :
    CoreOpsTry.branch (core.result.Result.Err x : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err x)) := rfl

@[simp] theorem from_residual_eq {T : Type} (x : core.io.error.Error) :
    CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame core.io.error.Error)
      (core.result.Result.Err x) = ok (core.result.Result.Err x) := by
  simp [CoreOpsTry_traitFromResidualResult.from_residual]

end mysql_common.CAUtil

namespace mysql_common.CAUtil

@[simp] theorem MysqlOldPassword_name_val : packets.MYSQL_OLD_PASSWORD_PLUGIN_NAME.val = utf8 "mysql_old_password" := by
  unfold packets.MYSQL_OLD_PASSWORD_PLUGIN_NAME; decide

theorem knownPlugin_MysqlOldPassword : knownPlugin (utf8 "mysql_old_password") = some .MysqlOldPassword := by
  rfl

@[simp] theorem MysqlClearPassword_name_val : packets.MYSQL_CLEAR_PASSWORD_PLUGIN_NAME.val = utf8 "mysql_clear_password" := by
  unfold packets.MYSQL_CLEAR_PASSWORD_PLUGIN_NAME; decide

theorem knownPlugin_MysqlClearPassword : knownPlugin (utf8 "mysql_clear_password") = some .MysqlClearPassword := by
  rfl

@[simp] theorem MysqlNativePassword_name_val : packets.MYSQL_NATIVE_PASSWORD_PLUGIN_NAME.val = utf8 "mysql_native_password" := by
  unfold packets.MYSQL_NATIVE_PASSWORD_PLUGIN_NAME; decide

theorem knownPlugin_MysqlNativePassword : knownPlugin (utf8 "mysql_native_password") = some .MysqlNativePassword := by
  rfl

@[simp] theorem Sha256Password_name_val : packets.SHA256_PASSWORD_PLUGIN_NAME.val = utf8 "sha256_password" := by
  unfold packets.SHA256_PASSWORD_PLUGIN_NAME; decide

theorem knownPlugin_Sha256Password : knownPlugin (utf8 "sha256_password") = some .Sha256Password := by
  rfl

@[simp] theorem CachingSha2Password_name_val : packets.CACHING_SHA2_PASSWORD_PLUGIN_NAME.val = utf8 "caching_sha2_password" := by
  unfold packets.CACHING_SHA2_PASSWORD_PLUGIN_NAME; decide

theorem knownPlugin_CachingSha2Password : knownPlugin (utf8 "caching_sha2_password") = some .CachingSha2Password := by
  rfl

@[simp] theorem Ed25519_name_val : packets.ED25519_PLUGIN_NAME.val = utf8 "client_ed25519" := by
  unfold packets.ED25519_PLUGIN_NAME; decide

theorem knownPlugin_Ed25519 : knownPlugin (utf8 "client_ed25519") = some .Ed25519 := by
  rfl

@[simp] theorem Parsec_name_val : packets.PARSEC_PLUGIN_NAME.val = utf8 "parsec" := by
  unfold packets.PARSEC_PLUGIN_NAME; decide

theorem knownPlugin_Parsec : knownPlugin (utf8 "parsec") = some .Parsec := by
  rfl

theorem knownPlugin_none (n : List U8) (h0 : n ≠ utf8 "mysql_old_password") (h1 : n ≠ utf8 "mysql_clear_password") (h2 : n ≠ utf8 "mysql_native_password") (h3 : n ≠ utf8 "sha256_password") (h4 : n ≠ utf8 "caching_sha2_password") (h5 : n ≠ utf8 "client_ed25519") (h6 : n ≠ utf8 "parsec") :
    knownPlugin n = none := by
  simp only [knownPlugin, knownPlugins, authPluginName, List.find?]
  simp [eq_comm (b := n), *]

theorem slice_u8_eq_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ b => b = true ↔ s1.val = s2.val ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ ?_)
  · intro b hb; rw [← Slice.eq_iff]; simpa using hb
  · intro x y; simp

theorem cow_into_vec_spec (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    misc.raw.cow_into_vec core.clone.CloneU8 c ⦃ v => v.val = cowList c ⦄ := by
  cases c with
  | Borrowed s =>
    unfold misc.raw.cow_into_vec
    simp only
    apply WP.spec_mono (alloc.slice.Slice.to_vec_spec _ s (by simp))
    intro v hv; simp [cowList, hv, alloc.vec.Vec.val]
  | Owned v => simp [misc.raw.cow_into_vec, cowList]

theorem dropTrailingNul_eq (l : List U8) (hl : 0 < l.length) :
    dropTrailingNul l = if (l[l.length - 1]'(by omega)).val = 0 then l.take (l.length - 1) else l := by
  unfold dropTrailingNul
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  simp [List.dropLast_eq_take]

theorem dropTrailingNul_append_zero (l : List U8) : dropTrailingNul (l ++ [byte 0]) = l := by
  simp [dropTrailingNul, byte]; rfl

theorem PluginFromBytes.isPluginNamed {n : List U8} {r : packets.AuthPlugin} (h : PluginFromBytes n r) :
    IsPluginNamed (dropTrailingNul n) r := by
  unfold PluginFromBytes at h; unfold IsPluginNamed
  split at h
  · exact h
  · obtain ⟨s, hs, hv⟩ := h; exact ⟨_, hs, hv⟩

/-- The "drop one trailing `0`" block shared by `from_bytes`, `plugin_uses_c_string_scramble` and
`plugin_data`. -/
theorem drop_nul_spec (nm : Slice U8) :
    (if Slice.len nm > 0#usize then do
        let i ← Slice.len nm - 1#usize
        let i1 ← Slice.index_usize nm i
        if i1 = 0#u8 then
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) nm { «end» := i }
        else ok nm
      else ok nm) ⦃ s => s.val = dropTrailingNul nm.val ⦄ := by
  split
  · step*
    all_goals rw [dropTrailingNul_eq _ (by scalar_tac)]
    · have hz : ((↑nm : List U8)[(↑nm : List U8).length - 1]'(by scalar_tac)).val = 0 := by
        have : (↑nm : List U8).length - 1 = i.val := by scalar_tac
        simp only [this]; rw [← i1_post, ‹i1 = 0#u8›]; rfl
      rw [ite_eq_left hz, s_post]
      have : (↑nm : List U8).length - 1 = i.val := by scalar_tac
      simp [this, List.slice]
    · have hz : ¬ ((↑nm : List U8)[(↑nm : List U8).length - 1]'(by scalar_tac)).val = 0 := by
        have : (↑nm : List U8).length - 1 = i.val := by scalar_tac
        simp only [this]; rw [← i1_post]; intro h; apply ‹¬i1 = 0#u8›; scalar_tac
      rw [ite_eq_right hz]
  · have : (↑nm : List U8) = [] := by
      rw [← List.length_eq_zero_iff]; scalar_tac
    simp [this, dropTrailingNul]

theorem knownPlugin_name {n : List U8} {p : packets.AuthPlugin} (h : knownPlugin n = some p) :
    authPluginName p = n := by
  unfold knownPlugin at h
  have := List.find?_some h
  simpa using this

theorem hasNul_iff (l : List U8) : hasNul l = true ↔ ∃ b ∈ l, b.val = 0 := by
  simp [hasNul]

@[step] theorem null_as_bytes_spec (self : misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple self
      ⦃ s => s.val = cowList self.1 ⦄ :=
  rawbytes_as_bytes_full _ _ rfl misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec self

/-- `buf.parse::<RawBytes<NullBytes>>(())` is `nulStrRead`. -/
theorem parse_null_bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = nulStrRead buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = nulStrRead buf.val)
  apply WP.spec_mono (misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'_pair] at h ⊢
  unfold nulStrRead
  by_cases hz : ∃ b ∈ buf.val, b.val = 0
  · rw [ite_eq_left hz] at h
    have : hasNul buf.val = true := (hasNul_iff _).mpr hz
    simp only [this, ite_true]
    simp [h.1, h.2]
  · rw [ite_eq_right hz] at h
    have : hasNul buf.val = false := by
      cases hh : hasNul buf.val
      · rfl
      · exact absurd ((hasNul_iff _).mp hh) hz
    simp only [this]
    simp [h.1, h.2]

theorem nulStrRead_nulStr (nm tail : List U8) (hn : NoNul nm) :
    nulStrRead (nulStr nm ++ tail) = (some nm, tail) := by
  have hb : beforeZero nm = nm := PBUtil.beforeZero_of_all nm hn
  have hz : beforeZero (nm ++ byte 0 :: tail) = nm := beforeZero_append_zero nm tail hn
  have hh : hasNul (nm ++ byte 0 :: tail) = true := by
    rw [hasNul_iff]; exact ⟨byte 0, by simp, by simp [byte]; rfl⟩
  simp [nulStr, nulStrRead, hb, hz, hh]

/-! ## Connect attributes (reading) -/

theorem checkedLenencInt_length_lt {bs rest : List U8} {n : Nat} (h : checkedLenencInt bs = (some n, rest)) :
    rest.length < bs.length := by
  cases bs with
  | nil => simp [checkedLenencInt] at h
  | cons b t =>
    simp only [checkedLenencInt] at h
    split at h
    · simp at h; rw [← h.2]; simp
    · split at h
      · rename_i n' r' hd
        simp at h; rw [← h.2]
        simp only [lenencIntDecode] at hd
        split at hd
        · simp at hd; rw [← hd.2]; simp
        · split at hd
          · simp only [readLE] at hd; split at hd <;> simp at hd; rw [← hd.2]; simp
          · split at hd
            · simp only [readLE] at hd; split at hd <;> simp at hd; rw [← hd.2]; simp
            · split at hd
              · simp only [readLE] at hd; split at hd <;> simp at hd; rw [← hd.2]; simp
              · simp at hd
      · simp at h

theorem checkedLenencStr_length_lt {bs rest k : List U8} (h : checkedLenencStr bs = (some k, rest)) :
    rest.length < bs.length := by
  unfold checkedLenencStr at h
  split at h
  · simp at h
  · rename_i n r hr
    have := checkedLenencInt_length_lt hr
    split at h
    · simp at h; rw [← h.2]; simp; omega
    · simp at h

/-- The loop reading the attribute entries, as `attrEntriesAux` (with enough fuel), inserting into
`attrs`. -/
theorem entries_spec (h64 : Target64) (fuel : Nat) (data : io.ParseBuf) (attrs : Trusted.ConnectAttrs)
    (hf : data.val.length ≤ fuel) :
    packets.deserialize_connect_attrs_entries data attrs ⦃ r _ =>
      match attrEntriesAux fuel data.val with
      | none => okPart r = none
      | some kvs => ∃ es : List (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit ×
            misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit),
          es.map (fun e => (cowList e.1.1, cowList e.2.1)) = kvs ∧
          okPart r = some (es.foldl (fun acc e => Trusted.connectAttrsInsert acc e.1 e.2) attrs) ⦄ := by
  induction fuel generalizing data attrs with
  | zero =>
    have hd : data.val = [] := List.length_eq_zero_iff.mp (by omega)
    unfold packets.deserialize_connect_attrs_entries
    step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
    have : b = true := by simpa [hd] using hb
    simp only [this, ite_true, attrEntriesAux]
    refine (WP.spec_ok _).mpr ?_
    exact ⟨[], rfl, rfl⟩
  | succ f ih =>
    unfold packets.deserialize_connect_attrs_entries
    step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
    cases hd : data.val with
    | nil =>
      have : b = true := by simpa [hd] using hb
      simp only [this, ite_true, attrEntriesAux]
      refine (WP.spec_ok _).mpr ?_
      exact ⟨[], rfl, rfl⟩
    | cons x xs =>
      have : b = false := by cases b <;> simp_all
      simp only [this, Bool.false_eq_true, ite_false, attrEntriesAux]
      rw [← hd]
      step with parse_lenenc_bytes_spec h64 as ⟨r1, d1, h1⟩
      cases r1 with
      | Err e =>
        simp only [okPart_Err, Option.map_none] at h1
        rw [← h1]; simp only [branch_err, bind_ok, from_residual_eq]
        exact (WP.spec_ok _).mpr rfl
      | Ok rb =>
        simp only [okPart_Ok, Option.map_some] at h1
        have l1 := checkedLenencStr_length_lt h1.symm
        rw [← h1]; simp only [branch_ok]
        step with parse_lenenc_bytes_spec h64 as ⟨r2, d2, h2⟩
        cases r2 with
        | Err e =>
          simp only [okPart_Err, Option.map_none] at h2
          rw [← h2]; simp only [branch_err, bind_ok, from_residual_eq]
          exact (WP.spec_ok _).mpr rfl
        | Ok rb1 =>
          simp only [okPart_Ok, Option.map_some] at h2
          have l2 := checkedLenencStr_length_lt h2.symm
          rw [← h2]; simp only [branch_ok, bind_ok, misc.trusted.connect_attrs_insert]
          apply WP.spec_mono (ih d2 (Trusted.connectAttrsInsert attrs rb rb1) (by omega))
          rintro ⟨r, rest⟩ hr
          simp only [WP.uncurry'_pair] at hr ⊢
          cases ha : attrEntriesAux f d2.val with
          | none => rw [ha] at hr; simpa [ha] using hr
          | some kvs =>
            rw [ha] at hr
            obtain ⟨es, hes, hr⟩ := hr
            simp only [Option.map_some]
            exact ⟨(rb, rb1) :: es, by simp [hes], by simpa using hr⟩

/-- `deserialize_connect_attrs` is `connectAttrsRead`. -/
theorem connect_attrs_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.deserialize_connect_attrs buf ⦃ r rest =>
      optMatch BuiltFrom (okPart r) (connectAttrsRead buf.val).1 ∧
        rest.val = (connectAttrsRead buf.val).2 ⦄ := by
  unfold packets.deserialize_connect_attrs
  step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r1, b1, h1⟩
  unfold connectAttrsRead
  cases r1 with
  | Err e =>
    simp only [okPart_Err, Option.map_none] at h1
    rw [← h1]; simp only [branch_err, bind_ok, from_residual_eq]
    exact (WP.spec_ok _).mpr ⟨by simp [optMatch], rfl⟩
  | Ok val =>
    simp only [okPart_Ok, Option.map_some] at h1
    rw [← h1]; simp only [CoreOpsTry.branch, bind_ok]
    obtain ⟨i, u⟩ := val
    simp only [lift, bind_ok]
    have hi : (UScalar.cast .Usize i).val = i.val := PBUtil.cast_usize_64 h64 i
    step with parse_usize_spec as ⟨r2, b2, h2⟩
    rw [hi] at h2
    split at h2
    · rename_i hle
      have hnlt : ¬ (↑b1 : List U8).length < i.val := by simp [Slice.length] at hle; omega
      simp only [hnlt, ite_false]
      obtain ⟨h2a, h2b⟩ := h2
      cases r2 with
      | Err e => simp at h2a
      | Ok pb =>
        simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h2a
        simp only [bind_ok, misc.trusted.connect_attrs_new]
        apply WP.spec_bind (entries_spec h64 i.val pb Trusted.connectAttrsNew (by rw [h2a]; simp))
        rintro ⟨r3, b3⟩ h3
        simp only [WP.uncurry'_pair] at h3
        refine (WP.spec_ok _).mpr ?_
        simp only [WP.uncurry'_pair]
        rw [h2a] at h3
        refine ⟨?_, h2b⟩
        cases ha : attrEntriesAux i.val ((↑b1 : List U8).take i.val) with
        | none => rw [ha] at h3; simp [h3, optMatch]
        | some kvs =>
          rw [ha] at h3
          obtain ⟨es, hes, hr⟩ := h3
          rw [hr]
          exact ⟨es, hes, rfl⟩
    · rename_i hlt
      have hnlt : (↑b1 : List U8).length < i.val := by simp [Slice.length] at hlt; omega
      simp only [hnlt, ite_true]
      obtain ⟨h2a, rfl⟩ := h2
      cases r2 with
      | Ok _ => simp at h2a
      | Err e =>
        simp only [bind_ok, from_residual_eq]
        exact (WP.spec_ok _).mpr ⟨by simp [optMatch], rfl⟩

/-! ## `AuthPlugin` -/

theorem from_bytes_spec' (nm : Slice U8) :
    packets.AuthPlugin.from_bytes nm ⦃ r => PluginFromBytes nm.val r ⦄ := by
  unfold packets.AuthPlugin.from_bytes
  apply WP.spec_bind (Pₘ := fun s : Slice U8 => s.val = dropTrailingNul nm.val)
  · exact drop_nul_spec nm
  · intro name1 hn1
    have key : ∀ (p : packets.AuthPlugin) (n : String), knownPlugin (utf8 n) = some p → name1.val = utf8 n →
        (ok p : Result packets.AuthPlugin) ⦃ r => PluginFromBytes nm.val r ⦄ := by
      intro p n hk he
      simp only [WP.spec_ok, PluginFromBytes, ← hn1, he, hk]
    step with slice_u8_eq_spec as ⟨b0, hb0⟩
    split
    · exact key _ _ knownPlugin_CachingSha2Password (by simpa using hb0.mp ‹_›)
    · have n0 : name1.val ≠ utf8 "caching_sha2_password" := by
        intro h; exact ‹¬b0 = true› (hb0.mpr (by simpa using h))
      step with slice_u8_eq_spec as ⟨b1, hb1⟩
      split
      · exact key _ _ knownPlugin_MysqlNativePassword (by simpa using hb1.mp ‹_›)
      · have n1 : name1.val ≠ utf8 "mysql_native_password" := by
          intro h; exact ‹¬b1 = true› (hb1.mpr (by simpa using h))
        step with slice_u8_eq_spec as ⟨b2, hb2⟩
        split
        · exact key _ _ knownPlugin_MysqlOldPassword (by simpa using hb2.mp ‹_›)
        · have n2 : name1.val ≠ utf8 "mysql_old_password" := by
            intro h; exact ‹¬b2 = true› (hb2.mpr (by simpa using h))
          step with slice_u8_eq_spec as ⟨b3, hb3⟩
          split
          · exact key _ _ knownPlugin_MysqlClearPassword (by simpa using hb3.mp ‹_›)
          · have n3 : name1.val ≠ utf8 "mysql_clear_password" := by
              intro h; exact ‹¬b3 = true› (hb3.mpr (by simpa using h))
            step with slice_u8_eq_spec as ⟨b4, hb4⟩
            split
            · exact key _ _ knownPlugin_Ed25519 (by simpa using hb4.mp ‹_›)
            · have n4 : name1.val ≠ utf8 "client_ed25519" := by
                intro h; exact ‹¬b4 = true› (hb4.mpr (by simpa using h))
              step with slice_u8_eq_spec as ⟨b5, hb5⟩
              split
              · exact key _ _ knownPlugin_Parsec (by simpa using hb5.mp ‹_›)
              · have n5 : name1.val ≠ utf8 "parsec" := by
                  intro h; exact ‹¬b5 = true› (hb5.mpr (by simpa using h))
                step with slice_u8_eq_spec as ⟨b6, hb6⟩
                split
                · exact key _ _ knownPlugin_Sha256Password (by simpa using hb6.mp ‹_›)
                · have n6 : name1.val ≠ utf8 "sha256_password" := by
                    intro h; exact ‹¬b6 = true› (hb6.mpr (by simpa using h))
                  simp only [WP.spec_ok, PluginFromBytes, ← hn1]
                  rw [knownPlugin_none _ n2 n3 n1 n6 n0 n4 n5]
                  exact ⟨name1, rfl, rfl⟩

theorem as_bytes_spec' (self : packets.AuthPlugin) :
    packets.AuthPlugin.as_bytes self ⦃ s => s.val = authPluginName self ⦄ := by
  unfold packets.AuthPlugin.as_bytes
  cases self <;> simp [authPluginName]
  exact cow_deref_spec _ _

theorem authplugin_deserialize_spec' (buf : io.ParseBuf) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ PluginFromBytes buf.val p) ∧ rest.val = [] ⦄ := by
  unfold packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.eat_all_spec as ⟨s, rest, hs, hr⟩
  step with from_bytes_spec' as ⟨ap, hap⟩
  simp only [okPart_Ok, Option.some.injEq, exists_eq_left']
  rw [← hs]; exact ⟨hap, hr⟩

/-! ## `COM_CHANGE_USER` helpers -/

@[simp] theorem CLIENT_PLUGIN_AUTH_val : constants.CapabilityFlags.CLIENT_PLUGIN_AUTH.val = CLIENT_PLUGIN_AUTH := by
  simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH, CLIENT_PLUGIN_AUTH]

@[simp] theorem CLIENT_CONNECT_ATTRS_val : constants.CapabilityFlags.CLIENT_CONNECT_ATTRS.val = CLIENT_CONNECT_ATTRS := by
  simp [constants.CapabilityFlags.CLIENT_CONNECT_ATTRS, CLIENT_CONNECT_ATTRS]

theorem noNul_beforeZero (l : List U8) : NoNul (beforeZero l) := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons x t ih =>
    intro b hb
    rw [beforeZero_cons] at hb
    split at hb
    · simp at hb
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · assumption
      · exact ih b hb

theorem dropTrailingNul_of_noNul (l : List U8) (h : NoNul l) : dropTrailingNul l = l := by
  unfold dropTrailingNul
  cases hl : l.getLast? with
  | none => rfl
  | some b =>
    have hb : b ∈ l := List.mem_of_getLast? hl
    simp [h b hb]

theorem IsPluginNamed.name_canonical {n : List U8} {r : packets.AuthPlugin} (h : IsPluginNamed n r) :
    authPluginName r = n ∧ PluginCanonical r := by
  have hn : authPluginName r = n := by
    unfold IsPluginNamed at h
    split at h
    · rename_i p hp; rw [h]; exact knownPlugin_name hp
    · obtain ⟨c, rfl, hc⟩ := h; exact hc
  refine ⟨hn, ?_⟩
  unfold PluginCanonical; rw [hn]; exact h

theorem noNul_of_nulStrRead {bs n : List U8} (h : (nulStrRead bs).1 = some n) : NoNul n := by
  unfold nulStrRead at h
  split at h
  · simp at h; rw [← h]; exact noNul_beforeZero bs
  · simp at h

theorem null_deser_borrowed (buf : io.ParseBuf) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r _ =>
      ∀ c, okPart r = some c → ∃ s, c = .Borrowed s ⦄ := by
  unfold misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with PBUtil.position_of_zero_ok as ⟨o, ho⟩
  cases o with
  | none =>
    simp only
    step*
    simp [okPart]
  | some i =>
    simp only at ho ⊢
    step with io.ParseBuf.eat_spec buf i (by scalar_tac) as ⟨out, b1, h1, h2⟩
    step with io.ParseBuf.skip_spec b1 1#usize (by simp [Slice.length, h2]; scalar_tac) as ⟨b2, h3⟩
    simp [okPart]

/-- `buf.parse::<RawBytes<NullBytes>>(())`: `nulStrRead`, and the bytes are borrowed. -/
theorem parse_null_bytes_borrowed (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = nulStrRead buf.val ∧
        ∀ rb, okPart r = some rb → ∃ s, rb.1 = .Borrowed s ⦄ := by
  apply WP.spec_and (parse_null_bytes_spec buf)
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  show misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize _ () buf ⦃ _ ⦄
  unfold misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize
  step with null_deser_borrowed as ⟨r, b, h⟩
  cases r with
  | Ok c =>
    simp only [CoreOpsTry.branch, bind_ok]
    obtain ⟨s, rfl⟩ := h c rfl
    refine (WP.spec_ok _).mpr ?_
    intro rb hrb
    simp only [okPart] at hrb
    cases hrb; exact ⟨s, rfl⟩
  | Err e =>
    simp only [CoreOpsTry.branch, bind_ok, from_residual_eq]
    refine (WP.spec_ok _).mpr ?_
    simp

/-- `parse_change_user_auth_plugin`: with `CLIENT_PLUGIN_AUTH`, the name by `nulStrRead`, parsed as
the plugin of that name (in normal form); without it, none. -/
theorem change_user_auth_plugin_spec (flags : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.parse_change_user_auth_plugin flags buf ⦃ r rest =>
      if hasFlag flags.val CLIENT_PLUGIN_AUTH then
        optMatch (fun (o : Option packets.AuthPlugin) n => ∃ p, o = some p ∧ authPluginName p = n ∧ PluginCanonical p)
          (okPart r) (nulStrRead buf.val).1 ∧ rest.val = (nulStrRead buf.val).2
      else okPart r = some none ∧ rest = buf ⦄ := by
  unfold packets.parse_change_user_auth_plugin
  step with caps_contains_spec as ⟨b, hb⟩
  simp only [CLIENT_PLUGIN_AUTH_val] at hb
  rw [← hb]
  split
  · step with parse_null_bytes_borrowed as ⟨r1, b1, h1, hbor⟩
    cases r1 with
    | Err e =>
      simp only [okPart_Err, Option.map_none] at h1
      rw [← h1]; simp only [branch_err, bind_ok, from_residual_eq]
      exact (WP.spec_ok _).mpr ⟨by simp [optMatch], rfl⟩
    | Ok rb =>
      simp only [okPart_Ok, Option.map_some] at h1
      obtain ⟨s, hs⟩ := hbor rb rfl
      rw [← h1]
      simp only [CoreOpsTry.branch, bind_ok]
      obtain ⟨c, u⟩ := rb
      simp only at hs ⊢
      subst hs
      have hpar : io.ParseBuf.parse packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple s () ⦃ r rest =>
          (∃ p, okPart r = some p ∧ PluginFromBytes s.val p) ∧ rest.val = [] ⦄ := by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by
          simp [packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE])]
        exact authplugin_deserialize_spec' s
      refine WP.spec_bind hpar ?_
      rintro ⟨r2, b2⟩ ⟨⟨p, hp, hpf⟩, _⟩
      cases r2 with
      | Err e => simp at hp
      | Ok q =>
        simp only [okPart_Ok, Option.some.injEq] at hp
        subst hp
        have hn : NoNul s.val := by
          have e1 := congrArg Prod.fst h1
          exact noNul_of_nulStrRead e1.symm
        have hnamed := CAUtil.PluginFromBytes.isPluginNamed hpf
        rw [dropTrailingNul_of_noNul _ hn] at hnamed
        refine (WP.spec_ok _).mpr ?_
        simp only [WP.uncurry'_pair, okPart_Ok]
        refine ⟨?_, by simp⟩
        exact ⟨q, rfl, IsPluginNamed.name_canonical hnamed⟩
  · exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩

/-- The plugin-name step of `changeUserMoreRead`. -/
def pnRead (caps : Nat) (bs : List U8) : Option (Option (List U8)) × List U8 :=
  if hasFlag caps CLIENT_PLUGIN_AUTH then
    match nulStrRead bs with
    | (none, r) => (none, r)
    | (some n, r) => (some (some n), r)
  else (some none, bs)

/-- The attributes step of `changeUserMoreRead`. -/
def attRead (caps : Nat) (bs : List U8) : Option (Option (List (List U8 × List U8))) × List U8 :=
  if hasFlag caps CLIENT_CONNECT_ATTRS then
    match connectAttrsRead bs with
    | (none, r) => (none, r)
    | (some kvs, r) => (some (some kvs), r)
  else (some none, bs)

theorem changeUserMoreRead_eq (caps : Nat) (bs : List U8) :
    changeUserMoreRead caps bs =
      if bs.length < 2 then (none, bs)
      else match pnRead caps (bs.drop 2) with
        | (none, r) => (none, r)
        | (some pn, r1) =>
          match attRead caps r1 with
          | (none, r) => (none, r)
          | (some kvs, r2) => (some (⟨leNat (bs.take 2), pn⟩, kvs), r2) := rfl

theorem plugin_step (flags : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.parse_change_user_auth_plugin flags buf ⦃ r rest =>
      rest.val = (pnRead flags.val buf.val).2 ∧
      match (pnRead flags.val buf.val).1 with
      | none => okPart r = none
      | some pn => ∃ o, okPart r = some o ∧ o.map authPluginName = pn ∧ ∀ p, o = some p → PluginCanonical p ⦄ := by
  apply WP.spec_mono (change_user_auth_plugin_spec flags buf)
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'_pair] at h ⊢
  unfold pnRead
  split at h
  · rename_i hf
    simp only [hf, ite_true]
    obtain ⟨h1, h2⟩ := h
    cases hn : nulStrRead buf.val with
    | mk o rr =>
      rw [hn] at h1 h2
      cases o with
      | none =>
        simp only at h1 h2 ⊢
        refine ⟨h2, ?_⟩
        cases hr : okPart r with
        | none => rfl
        | some _ => rw [hr] at h1; simp [optMatch] at h1
      | some n =>
        simp only at h1 h2 ⊢
        refine ⟨h2, ?_⟩
        cases hr : okPart r with
        | none => rw [hr] at h1; simp [optMatch] at h1
        | some o =>
          rw [hr] at h1
          obtain ⟨p, rfl, hpn, hpc⟩ := h1
          refine ⟨some p, rfl, by simp [hpn], ?_⟩
          intro q hq; cases hq; exact hpc
  · rename_i hf
    simp only [hf, Bool.false_eq_true, ite_false]
    obtain ⟨h1, rfl⟩ := h
    exact ⟨rfl, none, h1, rfl, by simp⟩

theorem opt_connect_attrs_step (h64 : Target64) (flags : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.parse_opt_connect_attrs flags buf ⦃ r rest =>
      rest.val = (attRead flags.val buf.val).2 ∧
      match (attRead flags.val buf.val).1 with
      | none => okPart r = none
      | some kvs => ∃ o, okPart r = some o ∧ AttrsMatch o kvs ⦄ := by
  unfold packets.parse_opt_connect_attrs attRead
  step with caps_contains_spec as ⟨b, hb⟩
  simp only [CLIENT_CONNECT_ATTRS_val] at hb
  rw [← hb]
  split
  · step with connect_attrs_spec h64 as ⟨r1, b1, h1, h2⟩
    cases hc : connectAttrsRead buf.val with
    | mk o rr =>
      rw [hc] at h1 h2
      cases r1 with
      | Err e =>
        refine (WP.spec_ok _).mpr ?_
        cases o with
        | none => simp [h2]
        | some kvs => simp [optMatch] at h1
      | Ok m =>
        refine (WP.spec_ok _).mpr ?_
        cases o with
        | none => simp [optMatch] at h1
        | some kvs =>
          simp only [okPart_Ok, optMatch] at h1
          simp only [WP.uncurry'_pair, h2, okPart_Ok, Option.some.injEq, exists_eq_left', true_and]
          exact h1
  · refine (WP.spec_ok _).mpr ?_
    simp [AttrsMatch]

/-! ## Connect attributes (writing) -/

/-- The body of the attributes on the wire (without the total length). -/
def attrsBody (kvs : List (List U8 × List U8)) : List U8 :=
  (kvs.map (fun kv => lenencStr kv.1 ++ lenencStr kv.2)).flatten

theorem attrsEnc_eq (kvs : List (List U8 × List U8)) :
    attrsEnc kvs = lenencInt (attrsBody kvs).length ++ attrsBody kvs := rfl

/-- The byte lists of the entries. -/
def pairVals (es : List (Slice U8 × Slice U8)) : List (List U8 × List U8) :=
  es.map (fun e => (e.1.val, e.2.val))

theorem attrsBody_cons (kv : List U8 × List U8) (kvs : List (List U8 × List U8)) :
    attrsBody (kv :: kvs) = lenencStr kv.1 ++ lenencStr kv.2 ++ attrsBody kvs := by
  simp [attrsBody]

theorem connect_attrs_len_spec (entries : Slice (Slice U8 × Slice U8)) (k : Nat) :
    ∀ (i : Usize) (acc : U64), entries.length - i.val = k → i.val ≤ entries.length →
      acc.val + (attrsBody (pairVals (entries.val.drop i.val))).length ≤ U64.max →
      packets.connect_attrs_len entries i acc ⦃ r =>
        r.val = acc.val + (attrsBody (pairVals (entries.val.drop i.val))).length ⦄ := by
  induction k with
  | zero =>
    intro i acc hk hi hb
    unfold packets.connect_attrs_len
    have hlt : ¬ i < Slice.len entries := by scalar_tac
    have hd : entries.val.drop i.val = [] := by simp [Slice.length] at hk hi ⊢; omega
    simp only [hlt, ite_false, hd]
    simp [pairVals, attrsBody]
  | succ k ih =>
    intro i acc hk hi hb
    unfold packets.connect_attrs_len
    have hlt : i < Slice.len entries := by scalar_tac
    have hil : i.val < entries.val.length := by scalar_tac
    have hd : entries.val.drop i.val = entries.val[i.val] :: entries.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hil
    rw [hd] at hb ⊢
    simp only [pairVals, List.map_cons, attrsBody_cons, List.length_append] at hb ⊢
    simp only [hlt, ite_true]
    step*
    rw [← s_post] at hb ⊢
    simp only at hb ⊢
    have hmax : U64.max = 2 ^ 64 - 1 := by scalar_tac
    step with misc.lenenc_str_len_spec s (by omega) as ⟨i3, hi3⟩
    step with misc.lenenc_str_len_spec s1 (by omega) as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    apply WP.spec_mono (ih i2 i6 (by simp [Slice.length] at hk ⊢; omega) (by simp [Slice.length] at hil ⊢; omega)
      (by rw [hi6, hi5, hi3, hi4, i2_post]; simp only [pairVals]; omega))
    intro r hr
    rw [hr, hi6, hi5, hi3, hi4, i2_post]; simp only [pairVals]; omega

theorem serialize_entries_spec (entries : Slice (Slice U8 × Slice U8)) (k : Nat) :
    ∀ (i : Usize) (buf : alloc.vec.Vec U8), entries.length - i.val = k → i.val ≤ entries.length →
      buf.length + (attrsBody (pairVals (entries.val.drop i.val))).length ≤ Usize.max →
      packets.serialize_connect_attrs_entries entries i buf ⦃ b =>
        b.val = buf.val ++ attrsBody (pairVals (entries.val.drop i.val)) ⦄ := by
  induction k with
  | zero =>
    intro i buf hk hi hb
    unfold packets.serialize_connect_attrs_entries
    have hlt : ¬ i < Slice.len entries := by scalar_tac
    have hd : entries.val.drop i.val = [] := by simp [Slice.length] at hk hi ⊢; omega
    simp only [hlt, ite_false, hd]
    simp [pairVals, attrsBody]
  | succ k ih =>
    intro i buf hk hi hb
    unfold packets.serialize_connect_attrs_entries
    have hlt : i < Slice.len entries := by scalar_tac
    have hil : i.val < entries.val.length := by scalar_tac
    have hd : entries.val.drop i.val = entries.val[i.val] :: entries.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hil
    rw [hd] at hb ⊢
    simp only [pairVals, List.map_cons, attrsBody_cons, List.length_append] at hb ⊢
    simp only [hlt, ite_true]
    step*
    rw [← s_post] at hb ⊢
    simp only at hb ⊢
    step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf (by omega) as ⟨b1, hb1⟩
    have l1 : b1.length = buf.length + (lenencStr s.val).length := by simp [alloc.vec.Vec.length, hb1]
    step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s1 b1 (by omega) as ⟨b2, hb2⟩
    have l2 : b2.length = buf.length + (lenencStr s.val).length + (lenencStr s1.val).length := by
      simp [alloc.vec.Vec.length, hb2, hb1]; omega
    step as ⟨i2, hi2⟩
    apply WP.spec_mono (ih i2 b2 (by simp [Slice.length] at hk ⊢; omega) (by scalar_tac)
      (by rw [l2, hi2]; simp only [pairVals]; omega))
    intro r hr
    rw [hr, hb2, hb1, hi2]; simp [pairVals]

theorem attrsEntries_eq (m : Trusted.ConnectAttrs) :
    attrsEntries m = pairVals (Trusted.connectAttrsEntries m).val := rfl

theorem serialize_connect_attrs_spec (m : Trusted.ConnectAttrs) (buf : alloc.vec.Vec U8)
    (h : buf.length + (attrsEnc (attrsEntries m)).length ≤ Usize.max) :
    packets.serialize_connect_attrs m buf ⦃ b => b.val = buf.val ++ attrsEnc (attrsEntries m) ⦄ := by
  unfold packets.serialize_connect_attrs
  simp only [misc.trusted.connect_attrs_entries, bind_ok]
  rw [attrsEntries_eq, attrsEnc_eq] at h ⊢
  simp only [List.length_append] at h
  have h64 := lt_two_pow_64_of_le_max (n := buf.length + ((lenencInt (attrsBody (pairVals (Trusted.connectAttrsEntries m).val)).length).length + (attrsBody (pairVals (Trusted.connectAttrsEntries m).val)).length)) h
  have hmax : U64.max = 2 ^ 64 - 1 := by scalar_tac
  have hdv : (alloc.vec.Vec.deref (Trusted.connectAttrsEntries m)).val = (Trusted.connectAttrsEntries m).val := by
    simp [alloc.vec.Vec.deref, Slice.from_val]
  step with connect_attrs_len_spec (alloc.vec.Vec.deref (Trusted.connectAttrsEntries m)) _ 0#usize 0#u64 rfl (by simp)
    (by rw [hdv]; simp; omega) as ⟨len, hlen⟩
  have hz : (0#usize : Usize).val = 0 := rfl
  simp only [hdv, List.drop_zero, zero_add] at hlen
  step with io.BufMutExt.put_lenenc_int_spec buf len (by rw [hlen]; omega) as ⟨b1, hb1⟩
  have l1 : b1.length = buf.length + (lenencInt len.val).length := by simp [alloc.vec.Vec.length, hb1]
  apply WP.spec_mono (serialize_entries_spec (alloc.vec.Vec.deref (Trusted.connectAttrsEntries m)) _ 0#usize b1 rfl (by simp)
    (by simp only [hdv, hz, List.drop_zero]; rw [l1, hlen]; omega))
  intro r hr
  simp only [hdv, hz, List.drop_zero] at hr
  rw [hr, hb1, hlen]; simp

theorem serialize_change_user_connect_attrs_spec (o : Option Trusted.ConnectAttrs) (buf : alloc.vec.Vec U8)
    (h : buf.length + (attrsEnc ((o.map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.serialize_change_user_connect_attrs o buf ⦃ b =>
      b.val = buf.val ++ attrsEnc ((o.map attrsEntries).getD []) ⦄ := by
  unfold packets.serialize_change_user_connect_attrs
  cases o with
  | none =>
    simp only [misc.trusted.connect_attrs_new, bind_ok]
    have he : attrsEntries Trusted.connectAttrsNew = [] := by
      rw [attrsEntries_eq, Trusted.connectAttrsEntries_new]; rfl
    simp only [Option.map_none, Option.getD_none] at h ⊢
    rw [← he] at h ⊢
    exact serialize_connect_attrs_spec _ buf h
  | some m =>
    simp only [Option.map_some, Option.getD_some] at h ⊢
    exact serialize_connect_attrs_spec m buf h

/-! ## `COM_CHANGE_USER` round trips (pure) -/

theorem nulStr_of_noNul (n : List U8) (h : NoNul n) : nulStr n = n ++ [byte 0] := by
  simp [nulStr, PBUtil.beforeZero_of_all n h]

theorem changeUserMoreRead_enc (caps : Nat) (m : ChangeUserMore) (kvs : List (List U8 × List U8))
    (tail : List U8) (hc : ChangeUserMore.Compatible caps m) (hl : (attrsEnc kvs).length < 2 ^ 64) :
    changeUserMoreRead caps (changeUserMoreEnc m kvs ++ tail) = (some (m, some kvs), tail) := by
  obtain ⟨hcs, hpn, hnn, hca⟩ := hc
  obtain ⟨cs, pn⟩ := m
  simp only at hcs hpn hnn
  have hle : leNat (leBytes 2 cs) = cs := by
    rw [PBUtil.leNat_leBytes]; exact Nat.mod_eq_of_lt (by simpa using hcs)
  have har : attRead caps (attrsEnc kvs ++ tail) = (some (some kvs), tail) := by
    unfold attRead; simp [hca, connectAttrsRead_attrsEnc kvs tail hl]
  have h2 := PBUtil.length_leBytes 2 cs
  rw [changeUserMoreRead_eq]
  cases pn with
  | none =>
    have hf : hasFlag caps CLIENT_PLUGIN_AUTH = false := by simpa using hpn.symm
    have e : changeUserMoreEnc ⟨cs, none⟩ kvs ++ tail = leBytes 2 cs ++ (attrsEnc kvs ++ tail) := by
      simp [changeUserMoreEnc]
    have hpr : pnRead caps (attrsEnc kvs ++ tail) = (some none, attrsEnc kvs ++ tail) := by
      simp [pnRead, hf]
    rw [e, List.drop_left' h2, List.take_left' h2, hpr]
    have : ¬ (leBytes 2 cs ++ (attrsEnc kvs ++ tail)).length < 2 := by simp [h2]; omega
    rw [ite_eq_right this]
    simp only [har, hle]
  | some n =>
    have hf : hasFlag caps CLIENT_PLUGIN_AUTH = true := by simpa using hpn.symm
    have hn : NoNul n := hnn n rfl
    have e : changeUserMoreEnc ⟨cs, some n⟩ kvs ++ tail = leBytes 2 cs ++ (nulStr n ++ (attrsEnc kvs ++ tail)) := by
      simp [changeUserMoreEnc, nulStr_of_noNul n hn]
    have hpr : pnRead caps (nulStr n ++ (attrsEnc kvs ++ tail)) = (some (some n), attrsEnc kvs ++ tail) := by
      simp [pnRead, hf, nulStrRead_nulStr n _ hn]
    rw [e, List.drop_left' h2, List.take_left' h2, hpr]
    have : ¬ (leBytes 2 cs ++ (nulStr n ++ (attrsEnc kvs ++ tail))).length < 2 := by simp [h2]; omega
    rw [ite_eq_right this]
    simp only [har, hle]

end mysql_common.CAUtil
