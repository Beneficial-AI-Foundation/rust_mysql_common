import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf
import Proofs.Defs.LemmasG

/-! Helper lemmas for the length-encoded-string session-state changes:
`Proofs/Packets/SessionStateChange/{Schema,Gtids,SystemVariable,Unsupported}.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.SBSsA

/-- `RawBytes::<LenEnc>::new(v)`: wraps `v.into()`. -/
theorem lenenc_new {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    misc.raw.bytes.RawBytes.new misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple
      into v ⦃ x => x.1 = c ⦄ := by
  rw [misc.raw.bytes.RawBytes.new_eq _ into v c h]
  exact (WP.spec_ok _).mpr rfl

/-- `String::from_utf8_lossy` meets `LossyUtf8Valid`. -/
theorem from_utf8_lossy_spec (s : Slice U8) :
    misc.trusted.from_utf8_lossy s ⦃ c => LossyUtf8Valid s.val c ⦄ := by
  unfold misc.trusted.from_utf8_lossy
  apply (WP.spec_ok _).mpr
  intro hu
  have hv := (Defs.isUtf8_iff_isValidUTF8 _).1 hu
  exact ⟨s, by simp [hv], rfl⟩

/-- `as_str` of a length-encoded `RawBytes`. -/
theorem lenenc_as_str (rb : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  apply WP.spec_bind (PCSUtil.lenenc_as_bytes rb)
  intro s hs
  rw [← hs]
  exact from_utf8_lossy_spec s

/-- `parse_unchecked::<RawBytes<LenEnc>>`: `checkedLenencStr`. -/
@[step]
theorem lenenc_parse_unchecked (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse_unchecked
      (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
        misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      checkedLenencStr buf.val = ((okPart r).map (fun rb => cowList rb.1), rest.val) ⦄ :=
  PCSUtil.lenenc_raw_deserialize' h64 buf

/-- `parse::<RawBytes<LenEnc>>` (no fixed size): `checkedLenencStr`. -/
@[step]
theorem lenenc_parse (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse
      (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
        misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      checkedLenencStr buf.val = ((okPart r).map (fun rb => cowList rb.1), rest.val) ⦄ := by
  have hs : (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple).SIZE = ok none := by
    simp only [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE,
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple]
    unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl
  rw [io.ParseBuf.parse_of_size_none _ _ _ hs]
  exact PCSUtil.lenenc_raw_deserialize' h64 buf

end mysql_common.SBSsA
