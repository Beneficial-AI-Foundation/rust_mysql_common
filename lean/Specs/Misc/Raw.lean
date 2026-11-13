import Proofs.Misc.Raw.SliceRef
import Proofs.Misc.Raw.Slice
import Proofs.Misc.Raw.Array
import Proofs.Misc.Raw.Skip
import Proofs.Misc.Raw.ParseBuf
import Proofs.Misc.Raw.Either
import Proofs.Misc.Raw.F64

/-!
# `src/misc/raw/mod.rs`
    `MyDeserialize`/`MySerialize` for byte slices and arrays, `f64`, `Skip<LEN>`, `ParseBuf` and
    `Either<T, U>`.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean` (`leNat`, `leBytes`, `okPart`).

    **Reading the statements.** The generic impls (`Either`) are stated as transfer lemmas: what the
    component impls guarantee carries over. Panics are stated as equations `f x = fail e`: `f x` stops with a Rust panic (it neither returns nor runs forever). `e` is the Aeneas library's label for the kind of panic (`.panic` in general, `.assertionFailure` for a failed `assert!`, `.undef` for an out-of-range `[n..]`); Rust does not distinguish them.

    **Not covered.** Derived impls (`Debug`, `Clone`, `PartialEq`, ...).

    **Behaviour to note.** `[u8; LEN]`, `Skip<LEN>` and `f64` deserialize do not check the length
    (their `SIZE` is fixed, and `parse` checks it); `Either::unwrap_left`/`unwrap_right` panic on the
    other variant (by design).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl MyDeserialize for &[u8]` -/

/-- `SIZE` is `None`. -/
recall SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq
/-- total; the given number `len` of bytes (the context), an error with the buffer unchanged if there are fewer. -/
recall SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (len : Usize) (buf : io.ParseBuf) :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec
/-! ### `impl MySerialize for [u8]` -/

/-- appends the bytes. -/
recall SliceU8.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : Slice U8)
    (buf : alloc.vec.Vec U8) (h : buf.length + self.length ≤ Usize.max) :
    SliceU8.Insts.Mysql_commonProtoMySerialize.serialize self buf
      ⦃ buf' => buf'.val = buf.val ++ self.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SliceU8.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `impls for [u8; LEN]` -/

/-- `MyDeserialize for [u8; LEN]`: `SIZE` is `Some(LEN)`. -/
recall ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for [u8; LEN]`: the next `LEN` bytes. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
recall ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).map (·.val) = some (buf.val.take LEN.val) ∧ rest.val = buf.val.drop LEN.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MyDeserialize for [u8; LEN]` panics on fewer than `LEN` bytes. -/
recall ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (LEN : Usize) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf = fail .panic

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
/-- `MySerialize for [u8; LEN]`: appends the bytes. -/
recall ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : Array U8 LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ self.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct Skip<LEN> and its impls` -/

/-- `MyDeserialize for Skip<LEN>`: `SIZE` is `Some(LEN)`. -/
recall misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq (LEN : Usize) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE LEN = some LEN

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for Skip<LEN>`: skips `LEN` bytes. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
recall misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (LEN : Usize) (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf ⦃ r rest =>
      (okPart r).isSome ∧ rest.val = buf.val.drop LEN.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MyDeserialize for Skip<LEN>` panics on fewer than `LEN` bytes. -/
recall misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (LEN : Usize) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize LEN () buf = fail .undef

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
/-- `MySerialize for Skip<LEN>`: appends `LEN` zero bytes. -/
recall misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec {LEN : Usize} (self : misc.raw.Skip LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ List.replicate LEN.val (byte 0) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Skip.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `impl MyDeserialize for ParseBuf` -/

/-- `SIZE` is `None`. -/
recall io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq :
    io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE = none

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq
/-- total; the given number `len` of bytes as a sub-buffer, an error with the buffer unchanged if there are fewer. -/
recall io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (len : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec
/-! ### `enum Either and its impls` -/

/-- `unwrap_left` on `Left(x)` is `x`. -/
recall misc.raw.Either.unwrap_left_left {T U : Type} (x : T) :
    misc.raw.Either.unwrap_left (misc.raw.Either.Left x : misc.raw.Either T U) = ok x

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.unwrap_left_left
/-- `unwrap_left` on `Right(_)` panics (by design). -/
recall misc.raw.Either.unwrap_left_right {T U : Type} (y : U) :
    misc.raw.Either.unwrap_left (misc.raw.Either.Right y : misc.raw.Either T U) = fail .panic

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.unwrap_left_right
/-- `unwrap_right` on `Right(y)` is `y`. -/
recall misc.raw.Either.unwrap_right_right {T U : Type} (y : U) :
    misc.raw.Either.unwrap_right (misc.raw.Either.Right y : misc.raw.Either T U) = ok y

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.unwrap_right_right
/-- `unwrap_right` on `Left(_)` panics (by design). -/
recall misc.raw.Either.unwrap_right_left {T U : Type} (x : T) :
    misc.raw.Either.unwrap_right (misc.raw.Either.Left x : misc.raw.Either T U) = fail .panic

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.unwrap_right_left
/-- `MyDeserialize for Either`: `SIZE` is `None`. -/
recall misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE_eq {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1) (i2 : proto.MyDeserialize U C2) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE i1 i2 = none

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE_eq
/-- `MyDeserialize for Either`: with context `Left(ctx)`, `T::deserialize(ctx)` wrapped in `Left`. -/
recall misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_left {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1)
    (i2 : proto.MyDeserialize U C2) (ctx : C1) (buf : io.ParseBuf)
    (Q : Option T → io.ParseBuf → Prop) (h : i1.deserialize ctx buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize i1 i2 (.Left ctx) buf ⦃ r rest =>
      ∃ o, Q o rest ∧ okPart r = o.map misc.raw.Either.Left ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_left
/-- `MyDeserialize for Either`: with context `Right(ctx)`, `U::deserialize(ctx)` wrapped in `Right`. -/
recall misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_right {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1)
    (i2 : proto.MyDeserialize U C2) (ctx : C2) (buf : io.ParseBuf)
    (Q : Option U → io.ParseBuf → Prop) (h : i2.deserialize ctx buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize i1 i2 (.Right ctx) buf ⦃ r rest =>
      ∃ o, Q o rest ∧ okPart r = o.map misc.raw.Either.Right ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_right
/-- `MySerialize for Either`: `Left(x)` serializes as `x`. -/
recall misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_left {T U : Type} (i1 : proto.MySerialize T) (i2 : proto.MySerialize U)
    (x : T) (buf : alloc.vec.Vec U8) :
    misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize i1 i2 (.Left x) buf = i1.serialize x buf

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_left
/-- `MySerialize for Either`: `Right(y)` serializes as `y`. -/
recall misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_right {T U : Type} (i1 : proto.MySerialize T) (i2 : proto.MySerialize U)
    (y : U) (buf : alloc.vec.Vec U8) :
    misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize i1 i2 (.Right y) buf = i2.serialize y buf

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_right
/-! ### `impls for f64` -/

/-- `MyDeserialize for f64`: `SIZE` is `Some(8)`. -/
recall F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 8#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for f64`: the double whose bit pattern is the next 8 bytes, little-endian. Unchecked: panics on a shorter buffer (`deserialize_panics`); `parse` checks. -/
recall F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (·.bits.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MyDeserialize for f64` panics on fewer than 8 bytes. -/
recall F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .panic

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms F64.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
/-- `MySerialize for f64`: appends the bit pattern, little-endian. -/
recall F64.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : F64) (buf : alloc.vec.Vec U8) (h : buf.length + 8 ≤ Usize.max) :
    F64.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 self.bits.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms F64.Insts.Mysql_commonProtoMySerialize.serialize_spec
end mysql_common
