import Defs
import Proofs.Util.Value

/-! Statements for `enum Value and its impls` (spec file: `Specs/Value.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MySerialize for Value`: appends the binary-protocol encoding `binEnc` (NULL appends
    nothing: NULLs go in the row's null bitmap). -/
theorem value.Value.Insts.Mysql_commonProtoMySerialize.serialize_spec (v : value.Value) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binEnc (Val.ofValue v)).length ≤ Usize.max) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize v buf ⦃ buf' => buf'.val = buf.val ++ binEnc (Val.ofValue v) ⦄ :=
  ValueUtil.serialize_spec' v buf h

/-- `bin_len`: the length of the binary encoding, exactly what `serialize` appends. Precondition:
    the `u64` length computation does not overflow (true of every real `Vec`). -/
theorem value.Value.bin_len_spec (v : value.Value)
    (h : (binEnc (Val.ofValue v)).length < 2 ^ 64) :
    value.Value.bin_len v ⦃ n => n.val = (binEnc (Val.ofValue v)).length ⦄ :=
  ValueUtil.bin_len_spec' v h

/-- `deserialize_text`: total; `textRead` (`0xFB` is NULL, anything else a length-encoded
    string; an error on an empty buffer, with the buffer unchanged). -/
theorem value.Value.deserialize_text_spec (h64 : Target64) (buf : io.ParseBuf) :
    value.Value.deserialize_text buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = textRead buf.val ⦄ :=
  ValueUtil.deserialize_text_spec' h64 buf

/-- `deserialize_text` reads a length-encoded string back as `Bytes` (its first byte is never `0xFB`). -/
theorem value.Value.deserialize_text_roundtrip (s tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencStr s ++ tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (.bytes s) ∧ rest.val = tail ⦄ :=
  ValueUtil.deserialize_text_roundtrip' s tail buf h

/-- `deserialize_text` reads `0xFB` as `NULL`, consuming just that byte. -/
theorem value.Value.deserialize_text_null (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte 0xFB :: tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some .null ∧ rest.val = tail ⦄ :=
  ValueUtil.deserialize_text_null' tail buf h

/-- `deserialize_bin`: for a supported column type, total; `binRead` for that type and the
    column's `UNSIGNED_FLAG` (see `Defs/Value.lean` for the formats and for how input the protocol
    does not define is read). -/
theorem value.Value.deserialize_bin_spec (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead ct (isUnsigned flags) buf.val ⦄ :=
  ValueUtil.deserialize_bin_spec' h64 ct flags hct buf

/-- **Crash path.** `deserialize_bin` panics (`unimplemented!("Unsupported column type")`) on
    the five unsupported column types, whatever the buffer. (The panic message's `fmt::Arguments`
    are built by Aeneas library functions that are defined and never fail, so this is an
    equation.) -/
theorem value.Value.deserialize_bin_unsupported (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = false) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf = fail .panic := by
  cases ct <;> simp [binSupported] at hct <;> simp [value.Value.deserialize_bin, ValueUtil.new_debug_eq, ValueUtil.args_new_eq]

/-- Round trip: `deserialize_bin` at a compatible column type (`binCompatible`) reads back what
    `serialize` writes, up to `binNorm` (integers reinterpreted by the column's signedness; a
    negative zero `Time` comes back positive). Everything else, including floats (bit for bit),
    dates and byte strings, comes back unchanged. -/
theorem value.Value.deserialize_bin_roundtrip (v : value.Value) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hc : binCompatible (Val.ofValue v) ct)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binEnc (Val.ofValue v) ++ tail) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (binNorm (isUnsigned flags) (Val.ofValue v)) ∧
      rest.val = tail ⦄ :=
  ValueUtil.deserialize_bin_roundtrip' v ct flags hc tail buf h

end mysql_common
