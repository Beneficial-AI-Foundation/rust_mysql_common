import Defs

/-! Statements for `impl BytesRepr for BareBytes<MAX_LEN>` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `BareBytes<MAX_LEN>::MAX_LEN`: `MAX_LEN`. -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN M = M := by
  sorry

/-- `BareBytes<MAX_LEN>::SIZE` is `None`. -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE M = none := by
  sorry

/-- `BareBytes<MAX_LEN>::serialize`: appends the bytes, truncated to `MAX_LEN` (no length is written: it is stored elsewhere). -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec (M : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + text.length ≤ Usize.max) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize M text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take M.val ⦄ := by
  sorry

/-- `BareBytes<MAX_LEN>::deserialize`: total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. (`MAX_LEN` is not checked.) -/
theorem misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec (M : Usize) (len : Usize) (buf : io.ParseBuf) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize M len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map cowList = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

end mysql_common
