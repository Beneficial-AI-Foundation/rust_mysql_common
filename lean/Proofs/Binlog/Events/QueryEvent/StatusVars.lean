import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Bytes.BareBytes

/-! Statements for `struct StatusVars and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `iter`: an iterator at position 0 over the block (its first 65535 bytes). -/
theorem binlog.events.query_event.StatusVars.iter_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.iter s ⦃ it => it.pos.val = 0 ∧ it.status_vars.val = (cowList s.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.StatusVars.iter binlog.events.query_event.StatusVarsIterator.new
  apply WP.spec_bind (misc.raw.bytes.RawBytes.as_bytes_spec _ 65535#usize (by simp [misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec]) s)
  intro sl hsl
  exact (WP.spec_ok _).mpr ⟨rfl, hsl⟩

/-- `get_status_var(key)`: the first variable with that key in the walk, if any. -/
theorem binlog.events.query_event.StatusVars.get_status_var_spec (s : binlog.events.query_event.StatusVars) (k : binlog.consts.StatusVarKey) :
    binlog.events.query_event.StatusVars.get_status_var s k ⦃ o => o.map (fun x => (statusVarKeyCode x.key, x.value.val)) =
      (statusVarsOf ((cowList s.1).take 65535)).find? (fun kv => kv.1 = statusVarKeyCode k) ⦄ := by
  sorry

/-- `into_owned`: the same bytes. -/
theorem binlog.events.query_event.StatusVars.into_owned_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.into_owned s ⦃ s' => cowList s'.1 = cowList s.1 ⦄ := by
  unfold binlog.events.query_event.StatusVars.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨rb, hrb⟩
  exact hrb

/-- `MyDeserialize` with the length `len`: total; that many bytes, an error with the buffer unchanged if fewer. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec (len : U16) (buf : io.ParseBuf) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize
  have hc : (UScalar.cast .Usize len).val = len.val := IntAndMisc.cast_usize_small len (by scalar_tac)
  simp only [lift, bind_ok]
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq, misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq])]
  have h := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize 65535#usize) (UScalar.cast .Usize len) buf
    (fun o rest => if (UScalar.cast .Usize len).val ≤ buf.length then
        o = some (buf.val.take (UScalar.cast .Usize len).val) ∧ rest.val = buf.val.drop (UScalar.cast .Usize len).val
      else o = none ∧ rest = buf)
    (by
      apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec 65535#usize (UScalar.cast .Usize len) buf)
      rintro ⟨r, rest⟩ hr
      split_ifs at hr ⊢
      · exact hr
      · exact ⟨by simp [hr.1], hr.2⟩)
  step with h as ⟨r, rest, hr⟩
  rw [hc] at hr
  cases r with
  | Ok rb =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply (WP.spec_ok _).mpr
    split_ifs at hr ⊢ <;> simp_all
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    split_ifs at hr ⊢ <;> simp_all

/-- `MySerialize`: the bytes, truncated to 65535. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec (s : binlog.events.query_event.StatusVars) (buf : alloc.vec.Vec U8) (h : buf.length + min (cowList s.1).length 65535 ≤ Usize.max) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize s buf ⦃ buf' => buf'.val = buf.val ++ (cowList s.1).take 65535 ⦄ := by
  unfold binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro sl hsl
  apply WP.spec_mono (misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec 65535#usize sl buf (by simp only [Slice.length, hsl]; exact h))
  intro b hb; simp [hb, hsl]

end mysql_common
