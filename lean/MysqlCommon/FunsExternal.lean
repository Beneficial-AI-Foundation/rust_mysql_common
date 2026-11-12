-- Hand-written: the external functions of the mysql_common translation (from FunsExternal_Template.lean).
module
public import Aeneas
public import MysqlCommon.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false
open mysql_common

/-! ## Floats: exact definitions on the bit pattern (see `F32`/`F64` in TypesExternal.lean).
    std defines `fN::from_le_bytes(b) = fN::from_bits(uN::from_le_bytes(b))` (same for `be`). -/

@[rust_fun "core::f32::{f32}::to_bits"]
def core.f32.F32.to_bits (x : F32) : Result Std.U32 := ok x.bits

@[rust_fun "core::f32::{f32}::from_le_bytes"]
def core.f32.F32.from_le_bytes (a : Array Std.U8 4#usize) : Result F32 :=
  ok ⟨core.num.U32.from_le_bytes a⟩

@[rust_fun "core::f32::{f32}::from_be_bytes"]
def core.f32.F32.from_be_bytes (a : Array Std.U8 4#usize) : Result F32 :=
  ok ⟨core.num.U32.from_be_bytes a⟩

@[rust_fun "core::f64::{f64}::to_bits"]
def core.f64.F64.to_bits (x : F64) : Result Std.U64 := ok x.bits

@[rust_fun "core::f64::{f64}::from_le_bytes"]
def core.f64.F64.from_le_bytes (a : Array Std.U8 8#usize) : Result F64 :=
  ok ⟨core.num.U64.from_le_bytes a⟩

@[rust_fun "core::f64::{f64}::from_be_bytes"]
def core.f64.F64.from_be_bytes (a : Array Std.U8 8#usize) : Result F64 :=
  ok ⟨core.num.U64.from_be_bytes a⟩

/-! ## `Cow<'_, [T]>` and its trait instances: the std bodies.
    (These cannot be patched into the crate: Aeneas fails on matching a `&Cow` whose
    `Borrowed` variant holds a shared borrow, see translation notes.) -/

/-- `impl Deref for Cow`: `match *self { Borrowed(b) => b, Owned(ref o) => o.borrow() }`. -/
@[rust_fun
  "alloc::borrow::{core::ops::deref::Deref<alloc::borrow::Cow<'0, @B, @Clause0_Owned>, @B>}::deref"]
def alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref
  {B : Type _} {Clause0_Owned : Type _} (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned) :
  alloc.borrow.Cow B Clause0_Owned → Result B
  | .Borrowed b => ok b
  | .Owned o => ToOwnedInst.coreborrowBorrowInst.borrow o

/-- `impl AsRef<T> for Cow<'_, T>`: `self` (deref coercion). -/
@[rust_fun
  "alloc::borrow::{core::convert::AsRef<alloc::borrow::Cow<'0, @T, @Clause0_Owned>, @T>}::as_ref"]
def alloc.borrow.Cow.Insts.CoreConvertAsRef.as_ref
  {T : Type _} {Clause0_Owned : Type _} (ToOwnedInst : alloc.borrow.ToOwned T Clause0_Owned)
  (c : alloc.borrow.Cow T Clause0_Owned) : Result T :=
  alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref ToOwnedInst c

/-- `impl Borrow<[T]> for Vec<T>`: `&self[..]`. -/
@[rust_fun "alloc::slice::{core::borrow::Borrow<alloc::vec::Vec<@T>, [@T]>}::borrow"]
def alloc.vec.Vec.Insts.CoreBorrowBorrowSlice.borrow
  {T : Type _} (A : Type _) (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref v)

/-- `impl ToOwned for [T]`: `self.to_vec()`. -/
@[rust_fun "alloc::slice::{alloc::borrow::ToOwned<[@T], alloc::vec::Vec<@T>>}::to_owned"]
def Slice.Insts.AllocBorrowToOwnedVec.to_owned
  {T : Type _} (corecloneCloneInst : core.clone.Clone T) (s : Slice T) :
  Result (alloc.vec.Vec T) :=
  alloc.slice.Slice.to_vec corecloneCloneInst s

/-! ## `Vec<T>` as a slice, and `Display` through a shared reference: the std bodies. -/

/-- `impl AsRef<[T]> for Vec<T>`: `self` (deref coercion). -/
@[rust_fun "alloc::vec::{core::convert::AsRef<alloc::vec::Vec<@T>, [@T]>}::as_ref"]
def alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type _} (A : Type _) (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref v)

/-- `impl AsMut<[T]> for Vec<T>`: `self` (deref-mut coercion). -/
@[rust_fun "alloc::vec::{core::convert::AsMut<alloc::vec::Vec<@T>, [@T]>}::as_mut"]
def alloc.vec.Vec.Insts.CoreConvertAsMutSlice.as_mut
  {T : Type _} (A : Type _) (v : alloc.vec.Vec T) :
  Result ((Slice T) × (Slice T → alloc.vec.Vec T)) :=
  ok (alloc.vec.Vec.deref_mut v)

/-- `impl<T: Display> Display for &T`: `Display::fmt(&**self, f)`. -/
@[rust_fun "core::fmt::{core::fmt::Display<&'0 @T>}::fmt"]
def Shared0T.Insts.CoreFmtDisplay.fmt
  {T : Type _} (DisplayInst : core.fmt.Display T) (x : T) (f : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  DisplayInst.fmt x f

/-! ## `Arc<T>`, modelled by its value (see `alloc.sync.Arc` in TypesExternal.lean). -/

/-- `Arc::new(x)`. -/
@[rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::new"]
def alloc.sync.Arc.new {T : Type _} (x : T) : Result (alloc.sync.Arc T) := ok x

/-- `impl Clone for Arc<T>`: another `Arc` to the same value. -/
@[rust_fun "alloc::sync::{core::clone::Clone<alloc::sync::Arc<@T>>}::clone"]
def alloc.sync.Arc.Insts.CoreCloneClone.clone
  {T : Type _} {A : Type _} (coreallocAllocatorCloneInst : core.alloc.AllocatorClone A)
  (x : alloc.sync.Arc T) : Result (alloc.sync.Arc T) :=
  ok x

/-- `impl Deref for Arc<T>`: the value. -/
@[rust_fun "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  {T : Type _} (A : Type _) (x : alloc.sync.Arc T) : Result T :=
  ok x

/-! ## Axioms -/

/-- [core::mem::size_of]: used only by `RawFlags::SIZE` (`size_of::<T::Bits>()` for a generic
    `T`), which a Lean definition cannot compute. Nothing is assumed about its value.
    Caveat: as a function of the *Lean* type, it identifies Rust types that Aeneas maps to the
    same Lean type (`T`, `&T`, `Box<T>`), e.g. `size_of::<&u8>` with `size_of::<u8>`. Only ever
    apply it to the integer `Bits` types of `RawFlags`, and never add axioms about its value for
    non-integer types. -/
@[rust_fun "core::mem::size_of"]
axiom core.mem.size_of (T : Type _) : Result Std.Usize

/-- An opaque `io::Error` built from a kind and a static message. Nothing is assumed about it. -/
axiom core.io.error.Error.ofMsg : core.io.error.ErrorKind → Str → core.io.error.Error

/-- An opaque `io::Error` built from a kind and an error value. Nothing is assumed about it. -/
axiom core.io.error.Error.ofError
  {E : Type _} (coreerrorErrorInst : core.error.Error E) :
  core.io.error.ErrorKind → E → core.io.error.Error

/-- [mysql_common::misc::io_error_msg] (opaque in Cargo.toml): `io::Error::new(kind, msg)`.
    Assumed not to fail (Aeneas treats allocation as infallible); the value is opaque. -/
noncomputable def misc.io_error_msg (kind : core.io.error.ErrorKind) (msg : Str) :
  Result core.io.error.Error :=
  ok (core.io.error.Error.ofMsg kind msg)

/-- [mysql_common::misc::io_error_from] (opaque in Cargo.toml): `io::Error::new(kind, err)`.
    Assumed not to fail; the value is opaque. -/
noncomputable def misc.io_error_from
  {E : Type _} (coreerrorErrorInst : core.error.Error E)
  (kind : core.io.error.ErrorKind) (err : E) : Result core.io.error.Error :=
  ok (core.io.error.Error.ofError coreerrorErrorInst kind err)

/-- [mysql_common::constants::{impl Display for UnknownStatusFlags}::fmt] (opaque in Cargo.toml):
    the error message (formats the raw value with `{:b}`). Only needed to build the `Error`
    instance passed to `io_error_from`, whose result is opaque. Nothing is assumed about it. -/
axiom constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt :
  constants.UnknownStatusFlags → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mysql_common::constants::{impl Display for UnknownColumnFlags}::fmt] (opaque in Cargo.toml):
    as for `UnknownStatusFlags`. Nothing is assumed about it. -/
axiom constants.UnknownColumnFlags.Insts.CoreFmtDisplay.fmt :
  constants.UnknownColumnFlags → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
