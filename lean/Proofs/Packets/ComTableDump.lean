import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Defs.LemmasG

/-! Statements for `struct ComTableDump and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

@[step] private theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  have e : misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d = ok () := by
    simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  rw [e]; exact (WP.spec_ok _).mpr trivial

private theorem u8bytes_as_bytes_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = (cowList rb.1).take 255 ⦄ := by
  have ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm rb)
  intro s hs; rw [hs, hmv]

private theorem u8bytes_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid ((cowList rb.1).take 255) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with u8bytes_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

private theorem u8bytes_ser (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U8Bytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + (u8LenStr ((cowList rb.1).take 255)).length ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf
      ⦃ b => b.val = buf.val ++ u8LenStr ((cowList rb.1).take 255) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  simp only [u8LenStr, List.length_cons, List.length_take] at h
  apply WP.spec_mono (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; omega))
  intro b hb
  rw [hb]
  simp [u8LenStr, Slice.length, hs, Nat.min_comm]

private theorem parse_u8bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = checkedLenPrefixed 1 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = checkedLenPrefixed 1 buf.val)
    (misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

private theorem checkedLenPrefixed_u8LenStr (s t : List U8) (hs : s.length ≤ 255) :
    checkedLenPrefixed 1 (u8LenStr s ++ t) = (some s, t) := by
  simp [checkedLenPrefixed, readLE, u8LenStr, leNat, byte_val, Nat.mod_eq_of_lt (by omega : s.length < 256)]

private theorem tableDumpRead_enc (db tbl : List U8) (hdb : db.length ≤ 255) (htbl : tbl.length ≤ 255)
    (tail : List U8) : tableDumpRead (tableDumpEnc db tbl ++ tail) = (some (db, tbl), tail) := by
  unfold tableDumpEnc
  rw [List.take_of_length_le hdb, List.take_of_length_le htbl]
  simp only [List.cons_append, List.append_assoc, tableDumpRead, byte_val]
  rw [ite_eq_right (by norm_num), checkedLenPrefixed_u8LenStr _ _ hdb]
  dsimp only
  rw [checkedLenPrefixed_u8LenStr _ _ htbl]


/-- `ComTableDump::new(database, table)`: the two names (`into()`, not truncated). -/
theorem packets.ComTableDump.new_spec {T1 T2 : Type}
    (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (database : T1) (table : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into database = ok c1) (h2 : into2.into table = ok c2) :
    packets.ComTableDump.new into1 into2 database table ⦃ t =>
      cowList t.database.1 = cowList c1 ∧ cowList t.table.1 = cowList c2 ⦄ := by
  unfold packets.ComTableDump.new
  step*

/-- `database_raw`: the database's effective bytes (at most the first 255). -/
theorem packets.ComTableDump.database_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.database_raw self ⦃ s => s.val = (cowList self.database.1).take 255 ⦄ := by
  exact u8bytes_as_bytes_spec _

/-- `database`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComTableDump.impl.database_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.database self ⦃ c => LossyUtf8Valid ((cowList self.database.1).take 255) c ⦄ := by
  exact u8bytes_as_str_spec _

/-- `table_raw`: the table's effective bytes (at most the first 255). -/
theorem packets.ComTableDump.table_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.table_raw self ⦃ s => s.val = (cowList self.table.1).take 255 ⦄ := by
  exact u8bytes_as_bytes_spec _

/-- `table`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComTableDump.impl.table_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.table self ⦃ c => LossyUtf8Valid ((cowList self.table.1).take 255) c ⦄ := by
  exact u8bytes_as_str_spec _

/-- `MySerialize for ComTableDump`: appends `tableDumpEnc` (`0x13`, the two names with 1-byte
    lengths, truncated to 255 bytes: documented). -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComTableDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tableDumpEnc (cowList self.database.1) (cowList self.table.1)).length ≤ Usize.max) :
    packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ tableDumpEnc (cowList self.database.1) (cowList self.table.1) ⦄ := by
  unfold packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [tableDumpEnc, List.length_cons, List.length_append] at h
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  step with u8bytes_ser as ⟨b2, h2⟩
  · simp [alloc.vec.Vec.length, h1] at *; omega
  apply WP.spec_mono (u8bytes_ser _ _ (by simp [alloc.vec.Vec.length, h1, h2] at *; omega))
  intro b hb
  rw [hb, h2, h1]
  simp [tableDumpEnc]
  rfl

/-- `MyDeserialize for ComTableDump`: `SIZE` is `None`. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ComTableDump`: total; `tableDumpRead`. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)), rest.val) =
        tableDumpRead buf.val ⦄ := by
  unfold packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize tableDumpRead
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec 19#u8
    packets.InvalidComTableDumpHeader.Insts.CoreErrorError packets.InvalidComTableDumpHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 1 := hl
    obtain ⟨a0, rest, hbuf⟩ : ∃ a0 rest, (↑buf : List U8) = a0 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: rest, _ => exact ⟨a0, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    simp [leNat] at h1a h1b
    simp only [CoreOpsTry.branch]
    cases r with
    | Err e =>
      have ha : a0.val ≠ 0x13 := by intro h; simp [h] at h1a
      rw [ite_eq_left ha, ← h1b]
      simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok hd =>
      have ha : a0.val = 0x13 := by simpa using h1a
      rw [ite_eq_right (by simp [ha])]
      simp only
      step with parse_u8bytes_spec as ⟨r2, buf2, h2⟩
      rw [h1b] at h2
      rw [← h2]
      cases r2 with
      | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok rb =>
      simp only [okPart_Ok, Option.map_some]
      step with parse_u8bytes_spec as ⟨r3, buf3, h3⟩
      rw [← h3]
      cases r3 with
      | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok rb1 => simp
  · obtain ⟨h1a, h1b⟩ := h1
    have : (↑buf : List U8) = [] := by simp only [Slice.length] at hl; exact List.eq_nil_of_length_eq_zero (by omega)
    rw [this]
    subst h1b
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, this]

/-- Round trip: names of at most 255 bytes, in the protocol layout, are read back. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (db tbl : List U8) (hdb : db.length ≤ 255) (htbl : tbl.length ≤ 255) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = tableDumpEnc db tbl ++ tail) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)) = some (db, tbl) ∧
      rest.val = tail ⦄ := by
  apply WP.spec_mono (packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  rw [h, tableDumpRead_enc _ _ hdb htbl] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
