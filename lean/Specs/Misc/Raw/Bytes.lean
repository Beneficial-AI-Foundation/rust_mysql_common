import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.Raw.Bytes.U32Bytes
import Proofs.Misc.Raw.Bytes.NullBytes
import Proofs.Misc.Raw.Bytes.EofBytes
import Proofs.Misc.Raw.Bytes.BareBytes
import Proofs.Misc.Raw.Bytes.FixedLengthText
import Proofs.Misc.Raw.Bytes.VarLen
import Proofs.Misc.Raw.Bytes.ConstBytes

/-!
# `src/misc/raw/bytes.rs`
    Byte strings (`RawBytes<T>`) and their wire representations (`BytesRepr` impls), and constant byte
    strings (`ConstBytes`).

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean` (`cowList`, `okPart`, `beforeZero`, `leBytes`),
    `Defs/LenEnc.lean` (`lenencStr`, `lenencInt`, `checkedLenencStr`, `checkedLenPrefixed`),
    `Defs/VarLen.lean` (`jsonbVarLenStrRead`).

    **Reading the statements.** `RawBytes` is stated generically over its representation `T`, given
    `T::MAX_LEN`; each `BytesRepr` impl has its `MAX_LEN`, `SIZE`, `serialize`, `deserialize` and, where
    it holds, the round trip `serialize` then `deserialize`. A `Cow` is read through `cowList`: the
    statements do not distinguish borrowed from owned.

    **Not covered.** `RawBytes::into_owned`, `RawBytes::as_str` (UTF-8 conversion), `From`,
    `PartialEq<[u8]>`, `Debug` (excluded from the translation in `Cargo.toml`, or not public API).

    **Behaviour to note.** `BytesRepr for VarLen` writes a lenenc length but reads a JSONB varlen
    length (they differ from length 128 on). `FixedLengthText::deserialize` does not check the length
    (it relies on `SIZE` and `parse`). `NullBytes::serialize` truncates at an embedded `0`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RawBytes and its impls` -/

/-- `RawBytes::new(text)`: wraps `text.into()`. -/
recall misc.raw.bytes.RawBytes.new_eq {T T2 Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (into : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (text : T2) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into text = ok c) :
    misc.raw.bytes.RawBytes.new inst into text = ok (c, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.new_eq`

/-- `is_empty`: whether the effective length (`len`) is 0. -/
recall misc.raw.bytes.RawBytes.is_empty_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.is_empty inst self ⦃ b => (b ↔ min (cowList self.1).length m.val = 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.is_empty_spec`

/-- `len`: the _effective_ length, `min(bytes.len(), T::MAX_LEN)` (documented). -/
recall misc.raw.bytes.RawBytes.len_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.len inst self ⦃ n => n.val = min (cowList self.1).length m.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.len_spec`

/-- `as_bytes`: the _effective_ bytes, the first `T::MAX_LEN`. -/
recall misc.raw.bytes.RawBytes.as_bytes_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.as_bytes inst self ⦃ s => s.val = (cowList self.1).take m.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.as_bytes_spec`

/-- `MySerialize for RawBytes<T>`: `T::serialize` of all the bytes (not just the effective
    ones; truncation, if any, is up to `T::serialize`). Stated for any property `P` that
    `T::serialize` guarantees. -/
recall misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (self : misc.raw.bytes.RawBytes T Ctx) (buf : alloc.vec.Vec U8)
    (P : alloc.vec.Vec U8 → Prop)
    (h : ∀ s : Slice U8, s.val = cowList self.1 → inst.serialize s buf ⦃ P ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ P ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for RawBytes<T>`: `SIZE` is `T::SIZE`. -/
recall misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE inst = inst.SIZE

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq`

/-- `MyDeserialize for RawBytes<T>`: `T::deserialize`, wrapped; whatever it guarantees about the
    bytes and the buffer carries over. -/
recall misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) (ctx : Ctx)
    (buf : io.ParseBuf) (Q : Option (List U8) → io.ParseBuf → Prop)
    (h : inst.deserialize ctx buf ⦃ r rest => Q ((okPart r).map cowList) rest ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize inst ctx buf ⦃ r rest => Q ((okPart r).map (fun rb => cowList rb.1)) rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec`

/-! ### `impl BytesRepr for LenEnc` -/

/-- `LenEnc::MAX_LEN`: `usize::MAX`. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `LenEnc::SIZE` is `None`. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `LenEnc::serialize`: appends the length-encoded string. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr text.val).length ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ lenencStr text.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `LenEnc::deserialize`: total; `checkedLenencStr` (with the lenenc quirk: `0xFB`/`0xFF` read as length 0, so as the empty string). -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) (h64 : Target64) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenencStr buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- Round trip: reads back the length-encoded string `s`. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencStr s ++ tail) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-! ### `impl BytesRepr for U8Bytes` -/

/-- `U8Bytes::MAX_LEN`: `255`. -/
recall misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `U8Bytes::SIZE` is `None`. -/
recall misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `U8Bytes::serialize`: appends a `u8` length and the bytes, truncated to 255 bytes (documented). -/
recall misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + min text.length 255 ≤ Usize.max) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ byte (min text.length 255) :: text.val.take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `U8Bytes::deserialize`: total; `checkedLenPrefixed 1`. -/
recall misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 1 buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- Round trip, for at most 255 bytes. -/
recall misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length ≤ 255) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte s.length :: s ++ tail) :
    misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-! ### `impl BytesRepr for U32Bytes` -/

/-- `U32Bytes::MAX_LEN`: `u32::MAX`. -/
recall misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `U32Bytes::SIZE` is `None`. -/
recall misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `U32Bytes::serialize`: appends a little-endian `u32` length and the bytes, truncated to `u32::MAX` bytes (documented). -/
recall misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + min text.length (2 ^ 32 - 1) ≤ Usize.max) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 (min text.length (2 ^ 32 - 1)) ++ text.val.take (2 ^ 32 - 1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `U32Bytes::deserialize`: total; `checkedLenPrefixed 4`. -/
recall misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = checkedLenPrefixed 4 buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- Round trip, for fewer than `2^32` bytes. -/
recall misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 2 ^ 32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 s.length ++ s ++ tail) :
    misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-! ### `impl BytesRepr for NullBytes` -/

/-- `NullBytes::MAX_LEN`: `usize::MAX`. -/
recall misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `NullBytes::SIZE` is `None`. -/
recall misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `NullBytes::serialize`: appends the bytes before the first `0` (all of them if there is none), then a `0`: a string containing `0` is silently truncated. -/
recall misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + text.length ≤ Usize.max) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ beforeZero text.val ++ [byte 0] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `NullBytes::deserialize`: total; the bytes before the first `0`, consuming the `0`; an error (its kind is not stated: `io::Error` is opaque; documented as `InvalidData`) with the buffer unchanged if there is no `0`. -/
recall misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      if ∃ b ∈ buf.val, b.val = 0 then
        (okPart r).map cowList = some (beforeZero buf.val) ∧
        rest.val = buf.val.drop ((beforeZero buf.val).length + 1)
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- Round trip, for strings without a `0` byte. -/
recall misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : ∀ b ∈ s, b.val ≠ 0) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = s ++ [byte 0] ++ tail) :
    misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-! ### `impl BytesRepr for EofBytes` -/

/-- `EofBytes::MAX_LEN`: `usize::MAX`. -/
recall misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN.val = Usize.max

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `EofBytes::SIZE` is `None`. -/
recall misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `EofBytes::serialize`: appends the bytes. -/
recall misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + text.length ≤ Usize.max) :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ text.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `EofBytes::deserialize`: total; the rest of the buffer. -/
recall misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map cowList = some buf.val ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-! ### `impl BytesRepr for BareBytes<MAX_LEN>` -/

/-- `BareBytes<MAX_LEN>::MAX_LEN`: `MAX_LEN`. -/
recall misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN M = M

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.MAX_LEN_spec`

/-- `BareBytes<MAX_LEN>::SIZE` is `None`. -/
recall misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq (M : Usize) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE M = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.SIZE_eq`

/-- `BareBytes<MAX_LEN>::serialize`: appends the bytes, truncated to `MAX_LEN` (no length is written: it is stored elsewhere). -/
recall misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec (M : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + text.length ≤ Usize.max) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize M text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take M.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.serialize_spec`

/-- `BareBytes<MAX_LEN>::deserialize`: total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. (`MAX_LEN` is not checked.) -/
recall misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec (M : Usize) (len : Usize) (buf : io.ParseBuf) :
    misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize M len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map cowList = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.BareBytes.Insts.Mysql_commonMiscRawBytesBytesReprUsize.deserialize_spec`

/-! ### `impl BytesRepr for FixedLengthText<LEN>` -/

/-- `FixedLengthText<LEN>::MAX_LEN`: `LEN`. -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN L = L

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `FixedLengthText<LEN>::SIZE` is `Some(LEN)`. -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq (L : Usize) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE L = some L

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `FixedLengthText<LEN>::serialize`: appends exactly `LEN` bytes: the text, truncated or right-padded with `0x00` (documented). -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (L : Usize) (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + L.val ≤ Usize.max) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize L text buf ⦃ buf' => buf'.val = buf.val ++ text.val.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `FixedLengthText<LEN>::deserialize`: the next `LEN` bytes, padding included. Unchecked (`SIZE` is `Some(LEN)`, so it uses `eat`): panics on a shorter buffer (`deserialize_panics`); `parse` checks (`parse_rawbytes_spec`). -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (L : Usize) (buf : io.ParseBuf) (h : L.val ≤ buf.length) :
    misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ r rest =>
      (okPart r).map cowList = some (buf.val.take L.val) ∧ rest.val = buf.val.drop L.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- `FixedLengthText<LEN>::deserialize` panics on fewer than `LEN` bytes. -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_panics (L : Usize) (buf : io.ParseBuf) (h : buf.length < L.val) :
    ¬ misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize L () buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_panics`

/-- `buf.parse::<RawBytes<FixedLengthText<LEN>>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.parse_rawbytes_spec (L : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      if L.val ≤ buf.length then
        (okPart r).map (fun rb => cowList rb.1) = some (buf.val.take L.val) ∧
        rest.val = buf.val.drop L.val
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.parse_rawbytes_spec`

/-- Round trip through `parse::<RawBytes<FixedLengthText<LEN>>>`: what `serialize` writes comes back padded/truncated to exactly `LEN` bytes (so it is the original text iff the text has `LEN` bytes). -/
recall misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (L : Usize) (text tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0) ++ tail) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize (misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple L)) buf () ⦃ r rest =>
      (okPart r).map (fun rb => cowList rb.1) =
        some (text.take L.val ++ List.replicate (L.val - min L.val text.length) (byte 0)) ∧
      rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.FixedLengthText.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-! ### `impl BytesRepr for VarLen` -/

/-- `VarLen::MAX_LEN`: `u32::MAX`. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec`

/-- `VarLen::SIZE` is `None`. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq`

/-- `VarLen::serialize`: **Bug (format mismatch).** Appends the length as a *length-encoded integer*
    (`put_lenenc_int`), not as a JSONB varlen integer, which is what `deserialize` reads. The two
    agree only for lengths below 128. From 128 on the first length byte has bit 7 set, so
    `deserialize` takes the following byte(s) as part of the length and can silently read a wrong
    length: e.g. a 200-byte string starting with `'a'` is read as having length 12488
    (`Defs.jsonbVarLenRead_lenencInt_misread`); see `roundtrip_fails`. No `u32::MAX` truncation
    either. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt text.length).length + text.length ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ lenencInt text.length ++ text.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec`

/-- `VarLen::deserialize`: total; a JSONB-varlen length then that many bytes (`jsonbVarLenStrRead`). -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = jsonbVarLenStrRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec`

/-- Round trip of `serialize` holds only for strings shorter than 128 bytes (see the bug on `serialize`). -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 128) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip`

/-- **Bug (format mismatch).** For `128 ≤ len < 251`, `deserialize` does not read back what
    `serialize` writes: it either fails or returns other bytes or leaves a different rest. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip_fails (s tail : List U8) (hs : 128 ≤ s.length ∧ s.length < 251)
    (buf : io.ParseBuf) (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => ((okPart r).map cowList, rest.val) ≠ (some s, tail) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip_fails`

/-! ### `struct ConstBytes and its impls` -/

/-- `MyDeserialize for ConstBytes<T, LEN>`: `SIZE` is `Some(LEN)`. -/
recall misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE d v = some LEN

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ConstBytes<T, LEN>`: reads `LEN` bytes (unchecked: panics on a shorter
    buffer, `deserialize_panics`; `parse` checks); `Ok` iff they are `T::VALUE`, else an error
    (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); consumed either
    way. (`T::VALUE` and `T::Error::default()` must not panic.) -/
recall misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (hd : v.coredefaultDefaultInst.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize d v () buf ⦃ r rest =>
      ((okPart r).isSome ↔ buf.val.take LEN.val = a.val) ∧ rest.val = buf.val.drop LEN.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MyDeserialize for ConstBytes<T, LEN>` panics on fewer than `LEN` bytes. -/
recall misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ¬ misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize d v () buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics`

/-- `buf.parse::<ConstBytes<T, LEN>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
recall misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (hd : v.coredefaultDefaultInst.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple d v) buf () ⦃ r rest =>
      if LEN.val ≤ buf.length then
        ((okPart r).isSome ↔ buf.val.take LEN.val = a.val) ∧ rest.val = buf.val.drop LEN.val
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec`

/-- `MySerialize for ConstBytes<T, LEN>`: appends `T::VALUE`. -/
recall misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T E : Type} {LEN : Usize}
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (self : misc.raw.bytes.ConstBytes T LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize v self buf ⦃ buf' => buf'.val = buf.val ++ a.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec`
end mysql_common
