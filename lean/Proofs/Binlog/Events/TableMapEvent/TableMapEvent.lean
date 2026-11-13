import Defs
import Proofs.Util.BinlogEvRows

/-! Statements for `struct TableMapEvent and its impls` (spec file: `Specs/Binlog/Events/TableMapEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.table_map_event.TableMapEvent.impl.table_id_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.table_id e = ok e.table_id.1 := by
  rfl

/-- `columns_count`. -/
theorem binlog.events.table_map_event.TableMapEvent.impl.columns_count_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.columns_count e = ok e.columns_count.1 := by
  rfl

/-- `json_column_count`: the number of `JSON` (245) column types. -/
theorem binlog.events.table_map_event.TableMapEvent.json_column_count_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.json_column_count e ⦃ n => n.val = (cowList e.columns_type.1).countP (fun b => b.val = 245) ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.json_column_count binlog.events.table_map_event.count_json_columns
  obtain ⟨c, u⟩ := e.columns_type
  step as ⟨ s, hs ⟩
  apply WP.spec_mono (BERUtil.json_loop s 0#usize 0#usize (by simp) (by simp))
  intro r hr
  simp [hr, hs]

/-- `database_name_raw`: the name, its first 255 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.database_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.database_name_raw e ⦃ s => s.val = (cowList e.database_name.1).take 255 ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.database_name_raw
  obtain ⟨m, hm, hv⟩ := PBUtil.spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm _)
  intro s hs
  rw [hs, hv]

/-- `table_name_raw`: the name, its first 255 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.table_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.table_name_raw e ⦃ s => s.val = (cowList e.table_name.1).take 255 ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.table_name_raw
  obtain ⟨m, hm, hv⟩ := PBUtil.spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm _)
  intro s hs
  rw [hs, hv]

/-- `get_raw_column_type(i)`: `Ok(None)` past the last column, the type with that code, or the unknown code as an error. -/
theorem binlog.events.table_map_event.TableMapEvent.get_raw_column_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_raw_column_type e i ⦃ r => match (cowList e.columns_type.1)[i.val]? with
      | none => r = .Ok none
      | some b => match columnTypeOfCode b.val with
        | some t => r = .Ok (some t)
        | none => r = .Err b ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.get_raw_column_type
  step with misc.raw.seq.RawSeq.get_spec as ⟨ o, ho ⟩
  cases o with
  | none => simp at ho; simp [List.getElem?_eq_none ho]
  | some x =>
    simp at ho
    simp only [misc.raw._const.RawConst.get_eq, constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec, ← ho]
    cases columnTypeOfCode x.1.val <;> simp

/-- `get_column_metadata(i)`: the metadata of column `i` (`tmMetaAt`). -/
theorem binlog.events.table_map_event.TableMapEvent.get_column_metadata_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_column_metadata e i ⦃ o => o.map (·.val) = tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val ⦄ := by
  exact BERUtil.col_meta_spec e i

/-- `get_column_type(i)`: as `get_raw_column_type`, but `DATE` is `NEWDATE`, and a `STRING` column with metadata has the real type of its first metadata byte (`tmStringRealType`; another value `x` is `BadColumnType::Unexpected(x | 0x30)`). -/
theorem binlog.events.table_map_event.TableMapEvent.get_column_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_column_type e i ⦃ r => match (cowList e.columns_type.1)[i.val]? with
      | none => r = .Ok none
      | some b => match columnTypeOfCode b.val with
        | none => r = .Err (.Unknown b)
        | some t =>
          if b.val = 10 then r = .Ok (some .MYSQL_TYPE_NEWDATE)
          else if b.val = 254 then
            match tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val with
            | none => r = .Ok (some t)
            | some m => match tmStringRealType (m.headD (byte 0)).val with
              | some t' => r = .Ok (some t')
              | none => r = .Err (.Unexpected (byte ((m.headD (byte 0)).val ||| 0x30)))
          else r = .Ok (some t) ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.get_column_type
  step with misc.raw.seq.RawSeq.get_spec as ⟨ o, ho ⟩
  cases o with
  | none => simp at ho; simp [List.getElem?_eq_none ho]
  | some x =>
    simp at ho
    rw [← ho]
    simp only [misc.raw._const.RawConst.get_eq, constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec, bind_ok]
    rcases hc : columnTypeOfCode x.1.val with _ | t
    · simp [binlog.events.table_map_event.BadColumnType.Insts.CoreConvertFromUnknownColumnType.from]
    · have hcode : columnTypeCode t = x.1.val := by
        have := List.find?_some hc; simpa using this
      have hS : columnTypeCode t = 254 → ∀ m, tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val = some m → m ≠ [] := by
        intro h254 m hm hnil
        have := BERUtil.tmMetaAt_string _ _ _ _ x.1 hm ho.symm (by rw [← hcode, h254])
        simp [hnil] at this
      apply WP.spec_bind (BERUtil.real_type_spec e i t hS)
      intro r hr
      rw [hcode] at hr
      simp only
      split_ifs at hr ⊢
      · subst hr; simp
      · rcases hm : tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val with _ | m
        · simp only [hm] at hr ⊢; subst hr; simp
        · simp only [hm] at hr ⊢
          rcases hs : tmStringRealType (m.headD (byte 0)).val with _ | t'
          · simp only [hs] at hr ⊢; subst hr; simp
          · simp only [hs] at hr ⊢; subst hr; simp
      · subst hr; simp

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.table_map_event.TableMapEvent.into_owned_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.into_owned e ⦃ e' => tmView e' = tmView e ⦄ := by
  unfold binlog.events.table_map_event.TableMapEvent.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb, h1 ⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb1, h2 ⟩
  step with misc.raw.seq.RawSeq.into_owned_spec U8.Insts.Mysql_commonMiscRawIntIntReprU8 (fun x => by rfl) as ⟨ rs, h3, _ ⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb2, h4 ⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb3, h5 ⟩
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb4, h6 ⟩
  simp [tmView, h1, h2, h3, h4, h5, h6]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `tmRead` with the FDE's table-map post-header length. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs tmView (tmRead (postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT) buf.val) r rest ⦄ := by
  exact BERUtil.tm_deser h64 ctx buf

/-- `MySerialize`: appends the layout `tmEnc`. (64-bit target, as configured). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tmEnc e).length ≤ Usize.max) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tmEnc e ⦄ := by
  exact BERUtil.tm_serialize64 h64 e buf h

/-- Round trip, for a consistent event (`TmConsistent`) with a table id below `2^48`, read with a post-header other than 6 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT ≠ 6) (buf : io.ParseBuf) (h : buf.val = tmEnc e) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map tmView = some (tmView e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (BERUtil.tm_deser h64 ctx buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'] at hr ⊢
  rw [h, Defs.tmRead_tmEnc e hc ht _ hp] at hr
  exact hr

/-- `BinlogEvent::EVENT_TYPE`: `TABLE_MAP_EVENT` (19). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TABLE_MAP_EVENT := by
  unfold binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: `tmLenCrate` (with the bitmap counted as `(n + 8) / 7` bytes: a bug). The metadata block is assumed to have a length-encoded length below `2^64`: `lenenc_str_len` is computed in `u64` and overflows (panics) otherwise. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64)
    (hm : (lenencStr (cowList e.columns_metadata.1)).length < 2 ^ 64) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = tmLenCrate e ⦄ := by
  exact BERUtil.tm_len_gen h64 e v hn hm

/-- **Upstream bug:** for a consistent event, `len` differs from the length `serialize` writes by `(n + 8) / 7 - (n + 7) / 8` (when under the cap). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_bug (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64)
    (hcap : (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ≤ evLenCap) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val + (e.columns_count.1.val + 7) / 8 = (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ⦄ := by
  obtain ⟨hdb, htb, hty, hnb⟩ := hc
  have hb61 : (e.columns_count.1.val + 7) / 8 ≤ 2 ^ 61 := BERUtil.bl_le _
  have hlen : (tmEnc e).length = 6 + 2 + (1 + min (cowList e.database_name.1).length 255) + 1 + (1 + min (cowList e.table_name.1).length 255) + 1 +
      (lenencInt e.columns_count.1.val).length + e.columns_count.1.val + (lenencStr (cowList e.columns_metadata.1)).length +
      (e.columns_count.1.val + 7) / 8 + (cowList e.optional_metadata.1).length := by
    simp only [tmEnc, u8Str, List.length_append, List.length_cons, List.length_take, length_leBytes, hty, hnb, List.length_nil]
    omega
  have hm : (lenencStr (cowList e.columns_metadata.1)).length < 2 ^ 64 := by
    simp only [evLenCap] at hcap; omega
  apply WP.spec_mono (BERUtil.tm_len_gen h64 e v hn hm)
  intro n hn'
  rw [hn']
  simp only [tmLenCrate, evLenCap] at hcap ⊢
  omega

/-- `BinlogStruct::len` panics (overflow of `columns_count as usize + 8`) for a column count of `2^64 - 8` or more. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_panics (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : 2 ^ 64 ≤ e.columns_count.1.val + 8) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = fail .integerOverflow := by
  exact BERUtil.tm_len_panics h64 e v hn

end mysql_common
