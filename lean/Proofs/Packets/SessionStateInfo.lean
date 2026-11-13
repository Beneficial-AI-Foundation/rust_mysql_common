import Defs

/-! Statements for `struct SessionStateInfo and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_owned`: the same type and data. -/
theorem packets.SessionStateInfo.into_owned_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.into_owned self ⦃ s => SsInfo.of s = SsInfo.of self ⦄ := by
  sorry

/-- `data_type`: the type. -/
theorem packets.SessionStateInfo.impl.data_type_eq (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.impl.data_type self = ok self.data_type.1 := by
  sorry

/-- `data_ref`: the raw data. -/
theorem packets.SessionStateInfo.data_ref_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.data_ref self ⦃ s => s.val = cowList self.data.1 ⦄ := by
  sorry

/-- `decode`: total; the data read as a change of the entry's type (`ssChangeRead`). Bytes of
    the data after the change are ignored. -/
theorem packets.SessionStateInfo.decode_spec (h64 : Target64) (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.decode self ⦃ r =>
      (okPart r).map SsChange.of = (ssChangeRead self.data_type.1 (cowList self.data.1)).1 ⦄ := by
  sorry

/-- `MyDeserialize for SessionStateInfo`: `SIZE` is `None`. -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for SessionStateInfo`: total; `ssInfoRead` (a type code 0–5, then the data as
    a length-encoded string). -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map SsInfo.of, rest.val) = ssInfoRead buf.val ⦄ := by
  sorry

/-- Round trip: an entry in the protocol layout (`ssInfoEnc`) is read back. -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (s : packets.SessionStateInfo) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = ssInfoEnc (SsInfo.of s) ++ tail) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SsInfo.of = some (SsInfo.of s) ∧ rest.val = tail ⦄ := by
  sorry

/-- `MySerialize for SessionStateInfo`: appends `ssInfoEnc` (the type code, then the data as a
    length-encoded string). -/
theorem packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SessionStateInfo) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssInfoEnc (SsInfo.of self)).length ≤ Usize.max) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssInfoEnc (SsInfo.of self) ⦄ := by
  sorry

end mysql_common
