import Proofs.Misc.LenencIntLen
import Proofs.Misc.LenencStrLen
import Proofs.Misc.ReadVarlenUint
import Proofs.Misc.WriteVarlenUint
import Proofs.Misc.VarlenUintSize
import Proofs.Misc.SplitVersion

/-!
# `src/misc/mod.rs`
    Lengths of length-encoded values, and the variable-length unsigned integers of the MySQL
    serialization library.

    **Configuration.** As in `Specs/Io.lean` (x86_64-unknown-linux-gnu, the features of
    `scripts/aeneas-translate.sh`).

    **Definitions used.** `Defs/LenEnc.lean` (`lenencInt`, `lenencStr`), `Defs/VarLen.lean`
    (`varlenUint`, `varlenUintSize`, `varlenUintDecode`), `Defs/Bytes.lean` (`okPart`),
    `Defs/Compression.lean` (`splitVersion`, `versionPart`), `Defs/Convert.lean` (`asciiInt`,
    `isDigit`). Facts about `splitVersion`: `Specs/DefsComp.lean`.

    **Trusted axioms.** None of ours: `split_version` reaches `btoi` through patch 40's helper,
    which has an exact Lean model (`Trusted.btoiUnsigned`, a definition).

    **Not covered.** The private helpers `dot_or_end`/`digits_end` (added by patch 125); `unexpected_buf_eof`,
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

/-- `write_varlen_uint`: appends the serialization-library encoding `varlenUint v` (`varlenUintSize v` bytes, 1 to 9; the buffer only needs room for those). -/
recall misc.write_varlen_uint_spec (buf : alloc.vec.Vec U8) (v : U64)
    (h : buf.length + varlenUintSize v.val ≤ Usize.max) :
    misc.write_varlen_uint buf v ⦃ buf' => buf'.val = buf.val ++ varlenUint v.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.write_varlen_uint_spec
/-! ### `fn varlen_uint_size` -/

/-- `varlen_uint_size(v)`: the number of bytes of the encoding (`(varlenUint v).length = varlenUintSize v` is `Defs.varlenUint_length`). -/
recall misc.varlen_uint_size_spec (v : U64) :
    misc.varlen_uint_size v ⦃ n => n.val = varlenUintSize v.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.varlen_uint_size_spec
/-! ### `fn split_version` and `fn split_version_inner` -/

/-- `split_version(version_str)`: total, exact on any input. It returns `splitVersion` (the crate's reading; no protocol defines it) of the string's bytes: the major and minor parts (before the first and second `.`), and the run of ASCII digits starting the third part, each a number in `0..=255`. It returns `(0, 0, 0)` if there are fewer than two `.` or a part is not such a number. **Quirks:**
    * a failure is indistinguishable from version `0.0.0`;
    * the first two parts may carry a sign (`"+5.-0.7"` gives `(5, 0, 7)`: a btoi quirk);
    * a part above 255 makes the whole result `(0, 0, 0)`.
    Stated for any `AsRef<[u8]>` whose `as_ref` returns. -/
recall misc.split_version_eq {T : Type} (inst : core.convert.AsRef T (Slice U8)) (x : T) (s : Slice U8)
    (hs : inst.as_ref x = ok s) :
    misc.split_version inst x = ok ((splitVersion s.val).getD (0#u8, 0#u8, 0#u8))

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.split_version_eq
/-- `split_version_inner(input)`: total; exactly `splitVersion`. -/
recall misc.split_version_inner_eq (input : Slice U8) :
    misc.split_version_inner input = ok (splitVersion input.val)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.split_version_inner_eq
end mysql_common
