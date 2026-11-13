import Defs

/-! Statements for `struct TableMapEvent and its impls` (spec file: `Specs/Binlog/Events/TableMapEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `table_id`. -/
theorem binlog.events.table_map_event.TableMapEvent.impl.table_id_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.table_id e = ok e.table_id.1 := by
  sorry

/-- `columns_count`. -/
theorem binlog.events.table_map_event.TableMapEvent.impl.columns_count_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.columns_count e = ok e.columns_count.1 := by
  sorry

/-- `json_column_count`: the number of `JSON` (245) column types. -/
theorem binlog.events.table_map_event.TableMapEvent.json_column_count_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.json_column_count e ⦃ n => n.val = (cowList e.columns_type.1).countP (fun b => b.val = 245) ⦄ := by
  sorry

/-- `database_name_raw`: the name, its first 255 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.database_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.database_name_raw e ⦃ s => s.val = (cowList e.database_name.1).take 255 ⦄ := by
  sorry

/-- `table_name_raw`: the name, its first 255 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.table_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.table_name_raw e ⦃ s => s.val = (cowList e.table_name.1).take 255 ⦄ := by
  sorry

/-- `get_raw_column_type(i)`: `Ok(None)` past the last column, the type with that code, or the unknown code as an error. -/
theorem binlog.events.table_map_event.TableMapEvent.get_raw_column_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_raw_column_type e i ⦃ r => match (cowList e.columns_type.1)[i.val]? with
      | none => r = .Ok none
      | some b => match columnTypeOfCode b.val with
        | some t => r = .Ok (some t)
        | none => r = .Err b ⦄ := by
  sorry

/-- `get_column_metadata(i)`: the metadata of column `i` (`tmMetaAt`). -/
theorem binlog.events.table_map_event.TableMapEvent.get_column_metadata_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_column_metadata e i ⦃ o => o.map (·.val) = tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val ⦄ := by
  sorry

/-- `get_column_type(i)`: as `get_raw_column_type`, but `DATE` is `NEWDATE`, and a `STRING` column with metadata has the real type of its first metadata byte (`tmStringRealType`; another value is `BadColumnType::Unexpected`). -/
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
              | none => ∃ x, r = .Err (.Unexpected x)
          else r = .Ok (some t) ⦄ := by
  sorry

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.table_map_event.TableMapEvent.into_owned_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.into_owned e ⦃ e' => tmView e' = tmView e ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; `tmRead` with the FDE's table-map post-header length. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs tmView (tmRead (postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT) buf.val) r rest ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `tmEnc`. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.table_map_event.TableMapEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tmEnc e).length ≤ Usize.max) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tmEnc e ⦄ := by
  sorry

/-- Round trip, for a consistent event (`TmConsistent`) with a table id below `2^48`, read with a post-header other than 6 bytes. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT ≠ 6) (buf : io.ParseBuf) (h : buf.val = tmEnc e) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map tmView = some (tmView e) ∧ rest.val = [] ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `TABLE_MAP_EVENT` (19). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TABLE_MAP_EVENT := by
  sorry

/-- `BinlogStruct::len`: `tmLenCrate` (with the bitmap counted as `(n + 8) / 7` bytes: a bug). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = tmLenCrate e ⦄ := by
  sorry

/-- **Upstream bug:** for a consistent event, `len` differs from the length `serialize` writes by `(n + 8) / 7 - (n + 7) / 8` (when under the cap). -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_bug (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64)
    (hcap : (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ≤ evLenCap) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val + (e.columns_count.1.val + 7) / 8 = (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ⦄ := by
  sorry

/-- `BinlogStruct::len` panics (overflow of `columns_count as usize + 8`) for a column count of `2^64 - 8` or more. -/
theorem binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_panics (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : 2 ^ 64 ≤ e.columns_count.1.val + 8) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = fail .integerOverflow := by
  sorry

end mysql_common
