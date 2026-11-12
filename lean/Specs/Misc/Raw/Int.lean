import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Int.I8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU24
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU48
import Proofs.Misc.Raw.Int.LeU56
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Int.LeI16
import Proofs.Misc.Raw.Int.LeI24
import Proofs.Misc.Raw.Int.LeI32
import Proofs.Misc.Raw.Int.LeI56
import Proofs.Misc.Raw.Int.LeI64
import Proofs.Misc.Raw.Int.LenEnc
import Proofs.Misc.Raw.Int.LeU32LowerHalf
import Proofs.Misc.Raw.Int.LeU32UpperHalf
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.ConstU32
import Proofs.Misc.Raw.Int.VarLen

/-!
# `src/misc/raw/int.rs`
    Integer wrappers (`RawInt<T>`) and their wire representations (`IntRepr` impls), constant integers
    (`ConstU8`, `ConstU32`) and the JSONB variable-length integer (`VarLen`).

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean`, `Defs/LenEnc.lean` (`lenencInt`, `checkedLenencInt`),
    `Defs/VarLen.lean` (`jsonbVarLen`, `jsonbVarLenRead`).

    **Reading the statements.** For each fixed-size representation: its `SIZE`, what `serialize`
    appends, what the (unchecked) `deserialize` reads, what the checked `parse::<RawInt<_>>` returns
    on any buffer, and the round trip `serialize` then `parse`. `IntRepr::Primitive` bounds are
    instances Aeneas passes along; they play no part in the statements.
    `¬ f x ⦃ _ => True ⦄` means `f x` does not return normally (it panics or does not terminate); every function stated this way here is loop-free, so it means `f x` panics, except `VarLen` `serialize_small_fails` (see its docstring).

    **Not covered.** `Debug` impls, derived impls (`Default`, `Clone`, `PartialEq`, `Ord`, `Hash`);
    `DerefMut for RawInt` (returns a mutable borrow; nothing to state beyond `Deref`).

    **Behaviour to note.** `LeI24` and `LeI56` do not round-trip negative values (the readers
    zero-extend). `VarLen::serialize` is broken: it never terminates for `x < 128` and writes a
    truncated encoding with its continuation bit set for `x ≥ 128`, so the reader runs on into the following bytes (see its statements). `ConstU8`/`ConstU32`
    deserialize do not check the buffer length (use `parse`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RawInt and its impls` -/

/-- `RawInt::new(x)` wraps `x`. -/
recall misc.raw.int.RawInt.new_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x = ok (x, ())

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.RawInt.new_eq
/-- `Deref for RawInt`: the wrapped value. -/
recall misc.raw.int.RawInt.deref_eq {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.int.RawInt T P) :
    misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref inst self = ok self.1

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.RawInt.deref_eq
/-- `MyDeserialize for RawInt<T>`: `SIZE` is `T::SIZE`. -/
recall misc.raw.int.RawInt.SIZE_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE inst = inst.SIZE

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.RawInt.SIZE_eq
/-- `MyDeserialize for RawInt<T>`: `T::deserialize`, wrapped; whatever `T::deserialize`
    guarantees about its result and the buffer carries over. -/
recall misc.raw.int.RawInt.deserialize_spec {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.RawInt.deserialize_spec
/-- `MySerialize for RawInt<T>`: `T::serialize` of the wrapped value. -/
recall misc.raw.int.RawInt.serialize_eq {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.int.RawInt T P) (buf : alloc.vec.Vec U8) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst self buf =
      inst.serialize self.1 buf

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.RawInt.serialize_eq
/-! ### `impl IntRepr for u8` -/

/-- `u8::SIZE` is `Some(1)`. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE = some 1#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq
/-- `u8::serialize`: appends `[x]`. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec (x : U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [x] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec
/-- `u8::deserialize`: reads 1 byte. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec
/-- `u8::deserialize` panics on fewer than 1 byte. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_panics
/-- `buf.parse::<RawInt<u8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec
/-- Round trip: `parse::<RawInt<u8>>` reads back what `RawInt::<u8>::serialize` writes. -/
recall U8.Insts.Mysql_commonMiscRawIntIntReprU8.roundtrip (x : U8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = [x] ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonMiscRawIntIntReprU8.roundtrip
/-! ### `impl IntRepr for i8` -/

/-- `i8::SIZE` is `Some(1)`. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE_eq :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE = some 1#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.SIZE_eq
/-- `i8::serialize`: appends `leBytesI 1 x.val`. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize_spec (x : I8) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 ≤ Usize.max) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 1 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.serialize_spec
/-- `i8::deserialize`: reads 1 byte. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_spec
/-- `i8::deserialize` panics on fewer than 1 byte. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.deserialize_panics
/-- `buf.parse::<RawInt<i8>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 1 byte. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 8 (leNat (buf.val.take 1))) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.parse_rawint_spec
/-- Round trip: `parse::<RawInt<i8>>` reads back what `RawInt::<i8>::serialize` writes. -/
recall I8.Insts.Mysql_commonMiscRawIntIntReprI8.roundtrip (x : I8) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 1 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple I8.Insts.Mysql_commonMiscRawIntIntReprI8) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonMiscRawIntIntReprI8.roundtrip
/-! ### `impl IntRepr for LeU16` -/

/-- `LeU16::SIZE` is `Some(2)`. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE = some 2#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.SIZE_eq
/-- `LeU16::serialize`: appends `leBytes 2 x.val`. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec (x : U16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec
/-- `LeU16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec
/-- `LeU16::deserialize` panics on fewer than 2 bytes. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_panics
/-- `buf.parse::<RawInt<LeU16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU16>>` reads back what `RawInt::<LeU16>::serialize` writes. -/
recall misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.roundtrip (x : U16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.roundtrip
/-! ### `impl IntRepr for LeU24` -/

/-- `LeU24::SIZE` is `Some(3)`. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 3#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq
/-- `LeU24::serialize`: appends `leBytes 3 x.val`. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 3 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec
/-- `LeU24::deserialize`: reads 3 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec
/-- `LeU24::deserialize` panics on fewer than 3 bytes. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics
/-- `buf.parse::<RawInt<LeU24>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 3 bytes. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 3)) ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU24>>` reads back what `RawInt::<LeU24>::serialize` writes. A `u32` above `2^24 - 1` loses its top byte. -/
recall misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 3 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 24) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip
/-! ### `impl IntRepr for LeU32` -/

/-- `LeU32::SIZE` is `Some(4)`. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 4#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq
/-- `LeU32::serialize`: appends `leBytes 4 x.val`. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec
/-- `LeU32::deserialize`: reads 4 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec
/-- `LeU32::deserialize` panics on fewer than 4 bytes. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics
/-- `buf.parse::<RawInt<LeU32>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 4 bytes. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU32>>` reads back what `RawInt::<LeU32>::serialize` writes. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip
/-! ### `impl IntRepr for LeU48` -/

/-- `LeU48::SIZE` is `Some(6)`. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 6#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq
/-- `LeU48::serialize`: appends `leBytes 6 x.val`. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 6 ≤ Usize.max) :
    misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 6 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
/-- `LeU48::deserialize`: reads 6 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 6 ≤ buf.length) :
    misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec
/-- `LeU48::deserialize` panics on fewer than 6 bytes. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 6) :
    ¬ misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics
/-- `buf.parse::<RawInt<LeU48>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 6 bytes. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 6 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 6)) ∧ rest.val = buf.val.drop 6
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU48>>` reads back what `RawInt::<LeU48>::serialize` writes. A `u64` above `2^48 - 1` loses its top bytes. -/
recall misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 6 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 48) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU48.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip
/-! ### `impl IntRepr for LeU56` -/

/-- `LeU56::SIZE` is `Some(7)`. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 7#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq
/-- `LeU56::serialize`: appends `leBytes 7 x.val`. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 ≤ Usize.max) :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 7 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
/-- `LeU56::deserialize`: reads 7 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec
/-- `LeU56::deserialize` panics on fewer than 7 bytes. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics
/-- `buf.parse::<RawInt<LeU56>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 7 bytes. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 7 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 7)) ∧ rest.val = buf.val.drop 7
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU56>>` reads back what `RawInt::<LeU56>::serialize` writes. A `u64` above `2^56 - 1` loses its top byte. -/
recall misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 7 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 56) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip
/-! ### `impl IntRepr for LeU64` -/

/-- `LeU64::SIZE` is `Some(8)`. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = some 8#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq
/-- `LeU64::serialize`: appends `leBytes 8 x.val`. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
/-- `LeU64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec
/-- `LeU64::deserialize` panics on fewer than 8 bytes. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics
/-- `buf.parse::<RawInt<LeU64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU64>>` reads back what `RawInt::<LeU64>::serialize` writes. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip
/-! ### `impl IntRepr for LeI16` -/

/-- `LeI16::SIZE` is `Some(2)`. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE_eq :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE = some 2#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.SIZE_eq
/-- `LeI16::serialize`: appends `leBytesI 2 x.val`. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize_spec (x : I16) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 2 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.serialize_spec
/-- `LeI16::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_spec
/-- `LeI16::deserialize` panics on fewer than 2 bytes. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.deserialize_panics
/-- `buf.parse::<RawInt<LeI16>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 16 (leNat (buf.val.take 2))) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeI16>>` reads back what `RawInt::<LeI16>::serialize` writes. -/
recall misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.roundtrip (x : I16) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI16.Insts.Mysql_commonMiscRawIntIntReprI16.roundtrip
/-! ### `impl IntRepr for LeI24` -/

/-- `LeI24::SIZE` is `Some(3)`. -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE = some 3#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq
/-- `LeI24::serialize`: appends `leBytesI 3 x.val`. -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec (x : I32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 3 ≤ Usize.max) :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 3 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec
/-- `LeI24::deserialize`: reads 3 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec (buf : io.ParseBuf) (h : 3 ≤ buf.length) :
    misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec
/-- `LeI24::deserialize` panics on fewer than 3 bytes. -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 3) :
    ¬ misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics
/-- `buf.parse::<RawInt<LeI24>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 3 bytes. -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (·.1.val) = some (((leNat (buf.val.take 3) : Nat) : Int)) ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeI24>>` reads back what `RawInt::<LeI24>::serialize` writes. **Not a round trip for negative values**: the reader (`eat_i24_le`) zero-extends, so `-1` comes back as `16777215` (and any `x` comes back as `x mod 2^24`, in `[0, 2^24)`). -/
recall misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip (x : I32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 3 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 24) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip
/-! ### `impl IntRepr for LeI32` -/

/-- `LeI32::SIZE` is `Some(4)`. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE = some 4#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.SIZE_eq
/-- `LeI32::serialize`: appends `leBytesI 4 x.val`. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec (x : I32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 4 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.serialize_spec
/-- `LeI32::deserialize`: reads 4 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_spec
/-- `LeI32::deserialize` panics on fewer than 4 bytes. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.deserialize_panics
/-- `buf.parse::<RawInt<LeI32>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 4 bytes. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 32 (leNat (buf.val.take 4))) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeI32>>` reads back what `RawInt::<LeI32>::serialize` writes. -/
recall misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip (x : I32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 4 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI32.Insts.Mysql_commonMiscRawIntIntReprI32.roundtrip
/-! ### `impl IntRepr for LeI56` -/

/-- `LeI56::SIZE` is `Some(7)`. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE = some 7#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq
/-- `LeI56::serialize`: appends `leBytesI 7 x.val`. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec (x : I64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 ≤ Usize.max) :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 7 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec
/-- `LeI56::deserialize`: reads 7 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec
/-- `LeI56::deserialize` panics on fewer than 7 bytes. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 7) :
    ¬ misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics
/-- `buf.parse::<RawInt<LeI56>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 7 bytes. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 7 ≤ buf.length then
        (okPart r).map (·.1.val) = some (((leNat (buf.val.take 7) : Nat) : Int)) ∧ rest.val = buf.val.drop 7
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeI56>>` reads back what `RawInt::<LeI56>::serialize` writes. **Not a round trip for negative values**: the reader (`eat_i56_le`) zero-extends, so any `x` comes back as `x mod 2^56`, in `[0, 2^56)`. -/
recall misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 7 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 56) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI56.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip
/-! ### `impl IntRepr for LeI64` -/

/-- `LeI64::SIZE` is `Some(8)`. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE = some 8#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.SIZE_eq
/-- `LeI64::serialize`: appends `leBytesI 8 x.val`. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec (x : I64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytesI 8 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.serialize_spec
/-- `LeI64::deserialize`: reads 8 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_spec
/-- `LeI64::deserialize` panics on fewer than 8 bytes. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    ¬ misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.deserialize_panics
/-- `buf.parse::<RawInt<LeI64>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 8 bytes. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      if 8 ≤ buf.length then
        (okPart r).map (·.1.val) = some (toSigned 64 (leNat (buf.val.take 8))) ∧ rest.val = buf.val.drop 8
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeI64>>` reads back what `RawInt::<LeI64>::serialize` writes. -/
recall misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip (x : I64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytesI 8 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeI64.Insts.Mysql_commonMiscRawIntIntReprI64.roundtrip
/-! ### `impl IntRepr for LenEnc` -/

/-- `LenEnc::SIZE` is `None` (variable length). -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq
/-- `LenEnc::serialize`: appends the length-encoded integer. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec (x : U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt x.val).length ≤ Usize.max) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize x buf ⦃ buf' => buf'.val = buf.val ++ lenencInt x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
/-- `LenEnc::deserialize`: total; `checked_eat_lenenc_int` (so `checkedLenencInt`, with its `0xFB`/`0xFF` quirk), `None` turned into an error. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = checkedLenencInt buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec
/-- `buf.parse::<RawInt<LenEnc>>(())`: total; `checkedLenencInt` (`SIZE` is `None`, so this is `deserialize`). -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ((okPart r).map (·.1.val), rest.val) = checkedLenencInt buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LenEnc>>` reads back what `RawInt::<LenEnc>::serialize` writes, for every `u64`. -/
recall misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip (x : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1) = some x ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip
/-! ### `impl IntRepr for LeU32LowerHalf` -/

/-- `LeU32LowerHalf::SIZE` is `Some(2)`. -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 2#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq
/-- `LeU32LowerHalf::serialize`: appends `leBytes 2 x.val`. -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec
/-- `LeU32LowerHalf::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec
/-- `LeU32LowerHalf::deserialize` panics on fewer than 2 bytes. -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics
/-- `buf.parse::<RawInt<LeU32LowerHalf>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU32LowerHalf>>` reads back what `RawInt::<LeU32LowerHalf>::serialize` writes. (The upper half of the `u32` is not stored, by design.) -/
recall misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 x.val ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val % 2 ^ 16) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32LowerHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip
/-! ### `impl IntRepr for LeU32UpperHalf` -/

/-- `LeU32UpperHalf::SIZE` is `Some(2)`. -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = some 2#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq
/-- `LeU32UpperHalf::serialize`: appends `leBytes 2 (x.val / 2 ^ 16)`. -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec (x : U32) (buf : alloc.vec.Vec U8)
    (h : buf.length + 2 ≤ Usize.max) :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ leBytes 2 (x.val / 2 ^ 16) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec
/-- `LeU32UpperHalf::deserialize`: reads 2 bytes. It does not check the length (documented: "`IntRepr::deserialize` won't check buffer length"), so it panics on a shorter buffer (`deserialize_panics`); `parse` (below) checks. -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      (okPart r).map (·.val) = some (leNat (buf.val.take 2) * 2 ^ 16) ∧ rest.val = buf.val.drop 2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec
/-- `LeU32UpperHalf::deserialize` panics on fewer than 2 bytes. -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 2) :
    ¬ misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_panics
/-- `buf.parse::<RawInt<LeU32UpperHalf>>(())`: total (checked through `SIZE`); an error with the buffer unchanged if it has fewer than 2 bytes. -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      if 2 ≤ buf.length then
        (okPart r).map (·.1.val) = some (leNat (buf.val.take 2) * 2 ^ 16) ∧ rest.val = buf.val.drop 2
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec
/-- Round trip: `parse::<RawInt<LeU32UpperHalf>>` reads back what `RawInt::<LeU32UpperHalf>::serialize` writes. (The lower half of the `u32` is not stored, by design.) -/
recall misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 2 (x.val / 2 ^ 16) ++ tail) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val / 2 ^ 16 * 2 ^ 16) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32UpperHalf.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip
/-! ### `struct ConstU8 and its impls` -/

/-- `ConstU8::new()`. -/
recall misc.raw.int.ConstU8.new_eq (T : Type) (N : U8) :
    misc.raw.int.ConstU8.new T N = ok ()

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.new_eq
/-- `ConstU8::value`: `N`. -/
recall misc.raw.int.ConstU8.value_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N) :
    misc.raw.int.ConstU8.value self ⦃ v => v = N ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.value_spec
/-- `MyDeserialize for ConstU8`: `SIZE` is `Some(1)`. -/
recall misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T : Type} (N : U8) (e : core.error.Error T) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE N e d = some 1#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for ConstU8`: reads 1 byte (unchecked: panics on a shorter buffer, `deserialize_panics`; `parse` checks), `Ok` iff they encode `N`, else an error (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); the bytes are consumed either way. (`T::default()` must not panic.) -/
recall misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = N.val) ∧ rest.val = buf.val.drop 1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MyDeserialize for ConstU8` panics on fewer than 1 byte. -/
recall misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
/-- `buf.parse::<ConstU8>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than 1 byte. -/
recall misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        ((okPart r).isSome ↔ leNat (buf.val.take 1) = N.val) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec
/-- `MySerialize for ConstU8`: appends `N`. -/
recall misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [N] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct ConstU32 and its impls` -/

/-- `ConstU32::new()`. -/
recall misc.raw.int.ConstU32.new_eq (T : Type) (N : U32) :
    misc.raw.int.ConstU32.new T N = ok ()

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.new_eq
/-- `MyDeserialize for ConstU32`: `SIZE` is `Some(4)`. -/
recall misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T : Type} (N : U32) (e : core.error.Error T) (d : core.default.Default T) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE N e d = some 4#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for ConstU32`: reads 4 bytes (unchecked: panics on a shorter buffer, `deserialize_panics`; `parse` checks), `Ok` iff they encode `N`, else an error (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); the bytes are consumed either way. (`T::default()` must not panic.) -/
recall misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 4) = N.val) ∧ rest.val = buf.val.drop 4 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MyDeserialize for ConstU32` panics on fewer than 4 bytes. -/
recall misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
/-- `buf.parse::<ConstU32>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than 4 bytes. -/
recall misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        ((okPart r).isSome ↔ leNat (buf.val.take 4) = N.val) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec
/-- `MySerialize for ConstU32`: appends `N`. -/
recall misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize_spec {T : Type} {N : U32} (self : misc.raw.int.ConstU32 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 N.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `impl IntRepr for VarLen` -/

/-- `VarLen::SIZE` is `None`. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq
/-- `VarLen::deserialize`: total; the JSONB varlen reader `jsonbVarLenRead` (at most 5 bytes,
    errors on more, on values above `u32::MAX`, and on end of input; the bytes read are consumed). -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = jsonbVarLenRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec
/-- `buf.parse::<RawInt<VarLen>>(())`: total; `jsonbVarLenRead` (`SIZE` is `None`, so this is `deserialize`). -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      ((okPart r).map (·.1.val), rest.val) = jsonbVarLenRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec
/-- `VarLen::deserialize` reads back the JSONB encoding `jsonbVarLen x` of every `u32`. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = jsonbVarLen x.val ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_roundtrip
/-- **Bug.** `VarLen::serialize` does not write the JSONB encoding. Its loop has its two
    branches swapped (it stops, setting the continuation bit, as soon as more bits remain): for
    `x ≥ 128` it appends the single byte `(x mod 128) | 0x80` and drops the higher bits. Since
    that byte has its continuation bit set, `deserialize` goes on into whatever bytes follow it
    and can silently return a wrong value; at the end of the input it fails. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_large (x : U32) (buf : alloc.vec.Vec U8) (hx : 128 ≤ x.val)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [byte (x.val % 128 + 128)] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_large
/-- **Bug.** For `x < 128`, `VarLen::serialize` never returns: after writing `x` its loop keeps
    appending `0` bytes forever (in Rust: until allocation fails and the process aborts; in the
    Lean model: until the `Vec` reaches `usize::MAX` and the next `push` fails). It is stated as
    "does not return normally" rather than as an equation because the failure only comes after
    `usize::MAX` iterations of the loop. -/
recall misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_small_fails (x : U32) (buf : alloc.vec.Vec U8) (hx : x.val < 128) :
    ¬ misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_small_fails
end mysql_common
