import Proofs.Misc.LenencIntLen
import Proofs.Misc.LenencStrLen
import Proofs.Misc.ReadVarlenUint
import Proofs.Misc.WriteVarlenUint
import Proofs.Misc.VarlenUintSize

/-!
# `src/misc/mod.rs`
    Lengths of length-encoded values, and the variable-length unsigned integers of the MySQL
    serialization library.

    **Configuration.** As in `Specs/Io.lean` (x86_64-unknown-linux-gnu, the features of
    `scripts/aeneas-translate.sh`).

    **Definitions used.** `Defs/LenEnc.lean` (`lenencInt`, `lenencStr`), `Defs/VarLen.lean`
    (`varlenUint`, `varlenUintSize`, `varlenUintDecode`), `Defs/Bytes.lean` (`okPart`).

    **Not covered.** `split_version` (string parsing, not translated); `unexpected_buf_eof`,
    `io_error_msg`, `io_error_from` (constructors of the opaque `io::Error`; the last two are opaque).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `fn lenenc_int_len` -/

/-- `lenenc_int_len(x)`: the length of the length-encoded integer `x` (1, 3, 4 or 9). -/
recall misc.lenenc_int_len_spec (x : U64) :
    misc.lenenc_int_len x ⦃ n => n.val = (lenencInt x.val).length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.lenenc_int_len_spec
/-! ### `fn lenenc_str_len` -/

/-- `lenenc_str_len(s)`: the length of the length-encoded string `s`. Precondition: that length
    fits in a `u64` (true of every real slice, whose length is at most `isize::MAX`). -/
recall misc.lenenc_str_len_spec (s : Slice U8) (h : (lenencStr s.val).length < 2 ^ 64) :
    misc.lenenc_str_len s ⦃ n => n.val = (lenencStr s.val).length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.lenenc_str_len_spec
/-! ### `fn read_varlen_uint` -/

/-- `read_varlen_uint`: total; the serialization-library decoder `varlenUintDecode`. On error
    (empty or truncated input) the buffer is unchanged. -/
recall misc.read_varlen_uint_spec (buf : io.ParseBuf) :
    misc.read_varlen_uint buf ⦃ r rest =>
      (okPart r).map (fun n => (n.val, rest.val)) = varlenUintDecode buf.val ∧
      (okPart r = none → rest = buf) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.read_varlen_uint_spec
/-- Round trip: `read_varlen_uint` reads back `varlenUint v` (what `write_varlen_uint` writes), for every `v : u64`. -/
recall misc.read_varlen_uint_roundtrip (v : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = varlenUint v.val ++ tail) :
    misc.read_varlen_uint buf ⦃ r rest => okPart r = some v ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.read_varlen_uint_roundtrip
/-! ### `fn write_varlen_uint` -/

/-- `write_varlen_uint`: appends the serialization-library encoding `varlenUint v` (1 to 9 bytes). -/
recall misc.write_varlen_uint_spec (buf : alloc.vec.Vec U8) (v : U64) (h : buf.length + 9 ≤ Usize.max) :
    misc.write_varlen_uint buf v ⦃ buf' => buf'.val = buf.val ++ varlenUint v.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.write_varlen_uint_spec
/-! ### `fn varlen_uint_size` -/

/-- `varlen_uint_size(v)`: the number of bytes of the encoding (`(varlenUint v).length = varlenUintSize v` is `Defs.varlenUint_length`). -/
recall misc.varlen_uint_size_spec (v : U64) :
    misc.varlen_uint_size v ⦃ n => n.val = varlenUintSize v.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.varlen_uint_size_spec
end mysql_common
