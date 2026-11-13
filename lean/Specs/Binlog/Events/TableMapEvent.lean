import Proofs.Binlog.Events.TableMapEvent.TableMapEvent

/-!
# `src/binlog/events/table_map_event.rs`
    `TableMapEvent` (`TABLE_MAP_EVENT`, code 19), without the optional-metadata API. Covered:
    `table_id`, `columns_count`, `json_column_count`, `database_name_raw`, `table_name_raw`,
    `get_raw_column_type`, `get_column_type` (with the `STRING` real-type rule), `get_column_metadata`
    (exact walk of the metadata block), `into_owned`, `SIZE`, `deserialize` (exact on any input),
    `serialize`, the round trip, `len` (exact, a bug), `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155, in
    particular 144: `get_column_metadata` as a recursion (stack proportional to the column
    index), 155). The reader and `len` statements take `Target64` (`columns_count as usize`).

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. When the reader fails, what it leaves of the buffer is not stated.

    **Definitions used.** `Defs/BinlogEvents.lean` (`TmView`, `tmView`, `tmEnc`, `tmRead`,
    `TmConsistent`, `tmLenCrate`, `tmColumnMetaLen`, `tmColumnMeta`, `tmMetaAt`,
    `tmStringRealType`, `u8Str`, `takeExact`, `optFst`, `postHeaderLen`, `fdeLens`, `evLenCap`,
    `ReadsAs`), `Defs/Flags.lean` (`columnTypeCode`, `columnTypeOfCode`), `Defs/LenEnc.lean`
    (`lenencInt`, `lenencStr`, `checkedLenencInt`, `checkedLenencStr`, `checkedLenPrefixed`),
    `Defs/Bytes.lean` (`Target64`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `null_bitmask` and `iter_optional_meta` and the optional-metadata types and
    iterators (`bitvec`; excluded), `database_name` / `table_name` (lossy UTF-8; excluded); the
    derived impls.

    **Behaviour to note (bug first).**
    * **`len` counts the NULL bitmap as `(columns_count + 8) / 7` bytes** instead of
      `(columns_count + 7) / 8` (`len_spec`, `len_bug`): it is wrong for every column count
      except 1–6 and 8 (e.g. one byte too many for 0 columns, `Defs.tmLenCrate_zero`). It also
      panics (overflow) for a column count within 8 of `2^64` (`len_panics`; such an event cannot
      be read from the wire).
    * The reader does not check the `0` after each name, nor that the metadata block matches the
      column types. Names are truncated to 255 bytes when written.
    * `get_column_type` reports `DATE` columns as `NEWDATE` (the binlog's `real_type`), and a
      `STRING` column as `ENUM`/`SET`/`STRING` from its first metadata byte (`tmStringRealType`;
      other values are an error).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct TableMapEvent and its impls` -/

/-- `table_id`. -/
recall binlog.events.table_map_event.TableMapEvent.impl.table_id_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.table_id e = ok e.table_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.impl.table_id_eq`

/-- `columns_count`. -/
recall binlog.events.table_map_event.TableMapEvent.impl.columns_count_eq (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.impl.columns_count e = ok e.columns_count.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.impl.columns_count_eq`

/-- `json_column_count`: the number of `JSON` (245) column types. -/
recall binlog.events.table_map_event.TableMapEvent.json_column_count_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.json_column_count e ⦃ n => n.val = (cowList e.columns_type.1).countP (fun b => b.val = 245) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.json_column_count_spec`

/-- `database_name_raw`: the name, its first 255 bytes. -/
recall binlog.events.table_map_event.TableMapEvent.database_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.database_name_raw e ⦃ s => s.val = (cowList e.database_name.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.database_name_raw_spec`

/-- `table_name_raw`: the name, its first 255 bytes. -/
recall binlog.events.table_map_event.TableMapEvent.table_name_raw_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.table_name_raw e ⦃ s => s.val = (cowList e.table_name.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.table_name_raw_spec`

/-- `get_raw_column_type(i)`: `Ok(None)` past the last column, the type with that code, or the unknown code as an error. -/
recall binlog.events.table_map_event.TableMapEvent.get_raw_column_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_raw_column_type e i ⦃ r => match (cowList e.columns_type.1)[i.val]? with
      | none => r = .Ok none
      | some b => match columnTypeOfCode b.val with
        | some t => r = .Ok (some t)
        | none => r = .Err b ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.get_raw_column_type_spec`

/-- `get_column_metadata(i)`: the metadata of column `i` (`tmMetaAt`). -/
recall binlog.events.table_map_event.TableMapEvent.get_column_metadata_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
    binlog.events.table_map_event.TableMapEvent.get_column_metadata e i ⦃ o => o.map (·.val) = tmMetaAt (cowList e.columns_type.1) (cowList e.columns_metadata.1) i.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.get_column_metadata_spec`

/-- `get_column_type(i)`: as `get_raw_column_type`, but `DATE` is `NEWDATE`, and a `STRING` column with metadata has the real type of its first metadata byte (`tmStringRealType`; another value is `BadColumnType::Unexpected`). -/
recall binlog.events.table_map_event.TableMapEvent.get_column_type_spec (e : binlog.events.table_map_event.TableMapEvent) (i : Usize) :
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
          else r = .Ok (some t) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.get_column_type_spec`

/-- `into_owned`: the same fields (now owned). -/
recall binlog.events.table_map_event.TableMapEvent.into_owned_spec (e : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.table_map_event.TableMapEvent.into_owned e ⦃ e' => tmView e' = tmView e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.into_owned_spec`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: total; `tmRead` with the FDE's table-map post-header length. -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (h64 : Target64) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs tmView (tmRead (postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT) buf.val) r rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec`

/-- `MySerialize`: appends the layout `tmEnc`. -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.table_map_event.TableMapEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tmEnc e).length ≤ Usize.max) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ tmEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip, for a consistent event (`TmConsistent`) with a table id below `2^48`, read with a post-header other than 6 bytes. -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .TABLE_MAP_EVENT ≠ 6) (buf : io.ParseBuf) (h : buf.val = tmEnc e) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map tmView = some (tmView e) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogEvent::EVENT_TYPE`: `TABLE_MAP_EVENT` (19). -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .TABLE_MAP_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

/-- `BinlogStruct::len`: `tmLenCrate` (with the bitmap counted as `(n + 8) / 7` bytes: a bug). -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = tmLenCrate e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

/-- **Upstream bug:** for a consistent event, `len` differs from the length `serialize` writes by `(n + 8) / 7 - (n + 7) / 8` (when under the cap). -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_bug (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (hc : TmConsistent e) (v : binlog.consts.BinlogVersion) (hn : e.columns_count.1.val + 8 < 2 ^ 64)
    (hcap : (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ≤ evLenCap) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val + (e.columns_count.1.val + 7) / 8 = (tmEnc e).length + (e.columns_count.1.val + 8) / 7 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_bug`

/-- `BinlogStruct::len` panics (overflow of `columns_count as usize + 8`) for a column count of `2^64 - 8` or more. -/
recall binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_panics (h64 : Target64) (e : binlog.events.table_map_event.TableMapEvent) (v : binlog.consts.BinlogVersion) (hn : 2 ^ 64 ≤ e.columns_count.1.val + 8) :
    binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogStruct.len_panics`

end mysql_common
