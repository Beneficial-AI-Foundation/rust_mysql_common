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

/-- `impl Clone for f32`: `*self` (a bitwise copy). Used by the derived `Clone for Value`. -/
@[rust_fun "core::clone::impls::{core::clone::Clone<f32>}::clone"]
def F32.Insts.CoreCloneClone.clone (x : F32) : Result F32 := ok x

/-- `impl Clone for f64`: `*self` (a bitwise copy). Used by the derived `Clone for Value`. -/
@[rust_fun "core::clone::impls::{core::clone::Clone<f64>}::clone"]
def F64.Insts.CoreCloneClone.clone (x : F64) : Result F64 := ok x

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

/-- `Option::as_ref` (`&Option<T>` to `Option<&T>`): the identity, since Aeneas translates a
    shared borrow as the value it points to. -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type _} (x : Option T) : Result (Option T) := ok x

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

/-- `Arc::make_mut(&mut a)`: a mutable reference to the value, which the `Arc` then holds. (std
    clones the value first when it is shared; through the operations above, a shared `Arc` and
    a clone of its value are indistinguishable, so the value model is exact.) -/
@[rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::make_mut"]
def alloc.sync.Arc.make_mut
  {T : Type _} {A : Type _} (corecloneCloneToUninitInst : core.clone.CloneToUninit T)
  (coreallocAllocatorCloneInst : core.alloc.AllocatorClone A) (a : alloc.sync.Arc T) :
  Result (T × (T → alloc.sync.Arc T)) :=
  ok (a, fun t => t)

/-- `impl Default for Arc<T>`: `Arc::new(T::default())`. -/
@[rust_fun "alloc::sync::{core::default::Default<alloc::sync::Arc<@T>>}::default"]
def alloc.sync.Arc.Insts.CoreDefaultDefault.default
  {T : Type _} (coredefaultDefaultInst : core.default.Default T) : Result (alloc.sync.Arc T) :=
  coredefaultDefaultInst.default

/-- [core::clone::{impl CloneToUninit for T: Clone}::clone_to_uninit]: writes a clone through a
    raw pointer. Only occurs as the `CloneToUninit` instance passed to `Arc::make_mut`, whose model
    above does not use it. Nothing is assumed about it. -/
@[rust_fun "core::clone::{core::clone::CloneToUninit<@T>}::clone_to_uninit"]
axiom core.clone.CloneToUninit.Blanket.clone_to_uninit
  {T : Type _} (CloneInst : core.clone.Clone T) :
  T → MutRawPtr Std.U8 → Result Unit

/-! ## Exact models of std items reached by the packets (`src/packets/`) -/

/-- `impl Clone for PhantomData<T>`: `PhantomData` (a unit). -/
@[rust_fun "core::marker::{core::clone::Clone<core::marker::PhantomData<@T>>}::clone"]
def core.marker.PhantomData.Insts.CoreCloneClone.clone
  {T : Type _} (x : core.marker.PhantomData T) : Result (core.marker.PhantomData T) :=
  ok x

/-- `impl Default for PhantomData<T>`: `PhantomData` (a unit). -/
@[rust_fun "core::marker::{core::default::Default<core::marker::PhantomData<@T>>}::default"]
def core.marker.PhantomData.Insts.CoreDefaultDefault.default
  (T : Type _) : Result (core.marker.PhantomData T) :=
  ok ()

/-- `impl Clone for Option<T>`: `None`, or `Some` of the clone. -/
@[rust_fun "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type _} (cloneCloneInst : core.clone.Clone T) : Option T → Result (Option T)
  | none => ok none
  | some x => do let y ← cloneCloneInst.clone x; ok (some y)

/-- `impl Default for Vec<T>`: `Vec::new()`. -/
@[rust_fun "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default
  (T : Type _) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- `char::is_ascii_lowercase`: `'a' ..= 'z'`. -/
@[rust_fun "core::char::methods::{char}::is_ascii_lowercase"]
def core.char.methods.Char.is_ascii_lowercase (c : Char) : Result Bool :=
  ok ('a' ≤ c && c ≤ 'z')

/-- `char::is_ascii_digit`: `'0' ..= '9'`. -/
@[rust_fun "core::char::methods::{char}::is_ascii_digit"]
def core.char.methods.Char.is_ascii_digit (c : Char) : Result Bool :=
  ok ('0' ≤ c && c ≤ '9')

/-- `str::as_bytes`: the bytes (`Str = Slice U8`). -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : Result (Slice Std.U8) := ok s

/-- `str::len`: the length in bytes. -/
@[rust_fun "core::str::{str}::len"]
def core.str.Str.len (s : Str) : Result Std.Usize := ok (Slice.len s)

/-- `str::is_empty`: `len() == 0`. -/
@[rust_fun "core::str::{str}::is_empty"]
def core.str.Str.is_empty (s : Str) : Result Bool := ok (s.val.length = 0)

/-- `impl Clone for Cow<B>`: `Borrowed(b)` stays borrowed; `Owned(o)` becomes
    `Owned(o.borrow().to_owned())`. -/
@[rust_fun
  "alloc::borrow::{core::clone::Clone<alloc::borrow::Cow<'0, @B, @Clause0_Owned>>}::clone"]
def alloc.borrow.Cow.Insts.CoreCloneClone.clone
  {B : Type _} {Clause0_Owned : Type _} (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned) :
  alloc.borrow.Cow B Clause0_Owned → Result (alloc.borrow.Cow B Clause0_Owned)
  | .Borrowed b => ok (.Borrowed b)
  | .Owned o => do
    let b ← ToOwnedInst.coreborrowBorrowInst.borrow o
    let o' ← ToOwnedInst.to_owned b
    ok (.Owned o')

/-- `Cow::into_owned`: `Borrowed(b)` gives `b.to_owned()`, `Owned(o)` gives `o`. -/
@[rust_fun "alloc::borrow::{alloc::borrow::Cow<'0, @B, @Clause0_Owned>}::into_owned"]
def alloc.borrow.Cow.into_owned
  {B : Type _} {Clause0_Owned : Type _} (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned) :
  alloc.borrow.Cow B Clause0_Owned → Result Clause0_Owned
  | .Borrowed b => ToOwnedInst.to_owned b
  | .Owned o => ok o

/-- `impl Default for Cow<B>`: `Owned(<B as ToOwned>::Owned::default())`. -/
@[rust_fun
  "alloc::borrow::{core::default::Default<alloc::borrow::Cow<'0, @B, @Clause0_Owned>>}::default"]
def alloc.borrow.Cow.Insts.CoreDefaultDefault.default
  {B : Type _} {Clause0_Owned : Type _} (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned)
  (coredefaultDefaultInst : core.default.Default Clause0_Owned) :
  Result (alloc.borrow.Cow B Clause0_Owned) := do
  let o ← coredefaultDefaultInst.default
  ok (.Owned o)

/-- `impl From<&[T]> for Cow<[T]>`: `Cow::Borrowed`. -/
@[rust_fun
  "alloc::vec::cow::{core::convert::From<alloc::borrow::Cow<'a, [@T], alloc::vec::Vec<@T>>, &'a [@T]>}::from"]
def alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice.from
  {T : Type _} (corecloneCloneInst : core.clone.Clone T) (s : Slice T) :
  Result (alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) :=
  ok (.Borrowed s)

/-- `impl From<Vec<T>> for Cow<[T]>`: `Cow::Owned`. -/
@[rust_fun
  "alloc::vec::cow::{core::convert::From<alloc::borrow::Cow<'a, [@T], alloc::vec::Vec<@T>>, alloc::vec::Vec<@T>>}::from"]
def alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec.from
  {T : Type _} (corecloneCloneInst : core.clone.Clone T) (v : alloc.vec.Vec T) :
  Result (alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) :=
  ok (.Owned v)

/-- `impl From<&str> for Cow<str>`: `Cow::Borrowed`. -/
@[rust_fun
  "alloc::string::{core::convert::From<alloc::borrow::Cow<'a, str, alloc::string::String>, &'a str>}::from"]
def alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr.from (s : Str) :
  Result (alloc.borrow.Cow Str String) :=
  ok (.Borrowed s)

/-- `impl From<String> for Cow<str>`: `Cow::Owned`. -/
@[rust_fun
  "alloc::string::{core::convert::From<alloc::borrow::Cow<'a, str, alloc::string::String>, alloc::string::String>}::from"]
def alloc.borrow.CowAStrString.Insts.CoreConvertFromString.from (s : String) :
  Result (alloc.borrow.Cow Str String) :=
  ok (.Owned s)

/-- `Arguments::from_str_nonconst`: as Aeneas' model of `Arguments::from_str`, formatting
    arguments are not modelled (`core.fmt.Arguments = Unit`). Only reached from the `Display`
    impls of packet-header errors, which build opaque `io::Error`s. -/
@[rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str_nonconst"]
def core.fmt.Arguments.from_str_nonconst : Str → Result core.fmt.Arguments := fun _ => ok ()

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
/-! ## Exact models of std / dependency items reached by the value conversions -/

/-- `impl TryFrom<Vec<T>> for [T; N]` (std): `Ok` of the elements when the length is `N`, else
    `Err` of the unchanged vector. -/
@[rust_fun
  "alloc::vec::{core::convert::TryFrom<[@T; @N], alloc::vec::Vec<@T>, alloc::vec::Vec<@T>>}::try_from"]
def Array.Insts.CoreConvertTryFromVecVec.try_from
  {T : Type _} (A : Type _) (N : Std.Usize) (v : alloc.vec.Vec T) :
  Result (core.result.Result (Array T N) (alloc.vec.Vec T)) :=
  if h : v.val.length = N.val then ok (.Ok (Array.from v.val h)) else ok (.Err v)

/-- [uuid::Uuid::from_bytes] (uuid 1.29.2, `const fn from_bytes(bytes: Bytes) -> Uuid { Uuid(bytes) }`;
    `uuid::Uuid` is translated as its field `[u8; 16]`). -/
@[rust_fun "uuid::builder::{uuid::Uuid}::from_bytes"]
def uuid.builder.Uuid.from_bytes (b : Array Std.U8 16#usize) : Result uuid.Uuid := ok b

/-! ## The trust boundary of the value conversions: `mysql_common::value::convert::trusted`

`translation-patches/40-value-convert-trusted-module.patch` adds this module; each function is
one call into a dependency (or a std function Aeneas does not model), and the module is `opaque`
in Cargo.toml. Each function gets one of:

* an **exact model** (a Lean `def` equal to the Rust function on every input): the UTF-8 checks,
  `String`/`str` byte conversions, integer `to_string`, `std::time::Duration`, `btoi`/`btou`,
  `time::Month`, and `time::error::Parse` construction;
* an **opaque value** with **partial specification axioms** (the axioms in `Trusted` below): the
  regexes (exact on ASCII input), the chrono and time constructors (success iff the components
  are valid) and getters;
* an **opaque value with no specification**: float parsing and widening, the parsers of time,
  num-bigint, rust_decimal, bigdecimal and serde_json, and their `From`/`to_string`.

`time::Duration` is the second kind, with **exact** axioms: an opaque getter `durNanos` and, per
operation, when it returns and the `durNanos` of the result.

Unless a declaration says otherwise, a helper is assumed not to panic (it returns `ok`). -/

namespace Trusted

/-- The bytes of a byte list, as a Lean `ByteArray`. -/
def bytesOf (l : List Std.U8) : ByteArray := ⟨(l.map fun b => UInt8.ofNat b.val).toArray⟩

/-- The bytes of a Lean `ByteArray`, as a list of `u8`. -/
def u8sOf (a : ByteArray) : List Std.U8 := a.data.toList.map fun b => (⟨b.toBitVec⟩ : Std.U8)

def isAsciiDigit (b : Std.U8) : Bool := 48 ≤ b.val && b.val ≤ 57

/-- A non-empty sequence of ASCII digits, as a number. -/
def decimalDigits? (l : List Std.U8) : Option Nat :=
  if !l.isEmpty && l.all isAsciiDigit then
    some (l.foldl (fun acc d => 10 * acc + (d.val - 48)) 0)
  else none

/-- The integer `btoi` reads: an optional `+`/`-` sign followed by `decimalDigits?`. -/
def btoiValue? : List Std.U8 → Option Int
  | [] => none
  | b :: rest =>
    if b.val = 43 then (decimalDigits? rest).map Int.ofNat
    else if b.val = 45 then (decimalDigits? rest).map fun n => -(n : Int)
    else (decimalDigits? (b :: rest)).map Int.ofNat

/-- `btoi::btoi::<T>` for a signed `T`. -/
def btoiSigned (ty : IScalarTy) (b : Slice Std.U8) : Option (IScalar ty) :=
  (btoiValue? b.val).bind (IScalar.tryMkOpt ty)

/-- `btoi::btoi::<T>` for an unsigned `T` (a `-` sign is accepted for the value 0). -/
def btoiUnsigned (ty : UScalarTy) (b : Slice Std.U8) : Option (UScalar ty) :=
  (btoiValue? b.val).bind fun v => if 0 ≤ v then UScalar.tryMkOpt ty v.toNat else none

/-- `btoi::btou::<T>`. -/
def btou (ty : UScalarTy) (b : Slice Std.U8) : Option (UScalar ty) :=
  (decimalDigits? b.val).bind (UScalar.tryMkOpt ty)

end Trusted

/-! ### std -/

/-- `std::str::from_utf8(bytes).ok()`: exact. A `&str` is its bytes (`Str = Slice U8`), and Lean's
    `ByteArray.IsValidUTF8` (the bytes are the UTF-8 encoding of a list of Unicode scalar values)
    is the definition of UTF-8 that std checks. -/
def value.convert.trusted.str_from_utf8 (bytes : Slice Std.U8) : Result (Option Str) :=
  ok (if (Trusted.bytesOf bytes.val).IsValidUTF8 then some bytes else none)

/-- `String::from_utf8(bytes)`, with the error's `into_bytes()`: exact (`String` is Lean's
    `String`, whose UTF-8 bytes are `bytes`). -/
def value.convert.trusted.string_from_utf8 (bytes : alloc.vec.Vec Std.U8) :
    Result (core.result.Result String (alloc.vec.Vec Std.U8)) :=
  ok (match String.fromUTF8? (Trusted.bytesOf bytes.val) with
    | some s => .Ok s
    | none => .Err bytes)

/-- `String::into_bytes`: exact (the `fail` branch is for a Lean string longer than
    `usize::MAX` bytes, which no Rust `String` is). -/
def value.convert.trusted.string_into_bytes (s : String) : Result (alloc.vec.Vec Std.U8) :=
  let l := Trusted.u8sOf s.toUTF8
  if h : l.length ≤ Usize.max then ok (alloc.vec.Vec.from l h) else fail .panic

/-- `str::as_bytes`: exact (`Str = Slice U8`). -/
def value.convert.trusted.str_as_bytes (s : Str) : Result (Slice Std.U8) := ok s

/-- `i128::to_string`: exact (decimal, with a leading `-` for negative values). -/
def value.convert.trusted.i128_to_string (x : Std.I128) : Result String := ok (toString x.val)

/-- `u128::to_string`: exact (decimal). -/
def value.convert.trusted.u128_to_string (x : Std.U128) : Result String := ok (toString x.val)

/-- `Duration::new(secs, nanos)`: exact (std: carries `nanos / 10^9` into `secs` with
    `checked_add(..).expect(..)`, keeps `nanos % 10^9`). -/
def value.convert.trusted.duration_new (secs : Std.U64) (nanos : Std.U32) :
    Result core.time.Duration :=
  if h : nanos.val < 1000000000 then ok ⟨secs, nanos, h⟩
  else
    match UScalar.tryMkOpt .U64 (secs.val + nanos.val / 1000000000) with
    | some s =>
      have hb : UScalar.inBounds .U32 (nanos.val % 1000000000) := by
        simp only [UScalar.inBounds, UScalarTy.numBits]; omega
      have hv : (UScalar.ofNatCore (ty := .U32) (nanos.val % 1000000000) hb).val < 1000000000 := by
        rw [UScalar.ofNatCore_val_eq]; omega
      ok ⟨s, UScalar.ofNatCore (nanos.val % 1000000000) hb, hv⟩
    | none => fail .panic

/-- `Duration::as_secs`: exact. -/
def value.convert.trusted.duration_as_secs (x : core.time.Duration) : Result Std.U64 := ok x.secs

/-- `Duration::subsec_nanos`: exact. -/
def value.convert.trusted.duration_subsec_nanos (x : core.time.Duration) : Result Std.U32 :=
  ok x.nanos

namespace Trusted
/-- `s.parse::<f32>().ok()`: opaque. -/
axiom parseF32 : Str → Option F32
/-- `s.parse::<f64>().ok()`: opaque. -/
axiom parseF64 : Str → Option F64
/-- `f64::from(x: f32)`: opaque (NaN payloads are not specified by Rust). -/
axiom f32ToF64 : F32 → F64
end Trusted

noncomputable def value.convert.trusted.str_parse_f32 (s : Str) : Result (Option F32) :=
  ok (Trusted.parseF32 s)
noncomputable def value.convert.trusted.str_parse_f64 (s : Str) : Result (Option F64) :=
  ok (Trusted.parseF64 s)
noncomputable def value.convert.trusted.f32_to_f64 (x : F32) : Result F64 := ok (Trusted.f32ToF64 x)

/-! ### btoi 0.5.0: exact

`btoi::<I>(b)` (and `btou`) accumulate the digits with `checked_mul`/`checked_add` (`checked_sub`
after a `-`); the accumulator's magnitude only grows, so it overflows exactly when the final value
is out of range. Only `Ok`/`Err` is observed (the helpers return `.ok()`). -/

def value.convert.trusted.btoi_i8 (b : Slice Std.U8) : Result (Option Std.I8) :=
  ok (Trusted.btoiSigned .I8 b)
def value.convert.trusted.btoi_i16 (b : Slice Std.U8) : Result (Option Std.I16) :=
  ok (Trusted.btoiSigned .I16 b)
def value.convert.trusted.btoi_i32 (b : Slice Std.U8) : Result (Option Std.I32) :=
  ok (Trusted.btoiSigned .I32 b)
def value.convert.trusted.btoi_i64 (b : Slice Std.U8) : Result (Option Std.I64) :=
  ok (Trusted.btoiSigned .I64 b)
def value.convert.trusted.btoi_i128 (b : Slice Std.U8) : Result (Option Std.I128) :=
  ok (Trusted.btoiSigned .I128 b)
def value.convert.trusted.btoi_isize (b : Slice Std.U8) : Result (Option Std.Isize) :=
  ok (Trusted.btoiSigned .Isize b)
def value.convert.trusted.btoi_u8 (b : Slice Std.U8) : Result (Option Std.U8) :=
  ok (Trusted.btoiUnsigned .U8 b)
def value.convert.trusted.btoi_u16 (b : Slice Std.U8) : Result (Option Std.U16) :=
  ok (Trusted.btoiUnsigned .U16 b)
def value.convert.trusted.btoi_u32 (b : Slice Std.U8) : Result (Option Std.U32) :=
  ok (Trusted.btoiUnsigned .U32 b)
def value.convert.trusted.btoi_u64 (b : Slice Std.U8) : Result (Option Std.U64) :=
  ok (Trusted.btoiUnsigned .U64 b)
def value.convert.trusted.btoi_u128 (b : Slice Std.U8) : Result (Option Std.U128) :=
  ok (Trusted.btoiUnsigned .U128 b)
def value.convert.trusted.btoi_usize (b : Slice Std.U8) : Result (Option Std.Usize) :=
  ok (Trusted.btoiUnsigned .Usize b)
def value.convert.trusted.btou_u8 (b : Slice Std.U8) : Result (Option Std.U8) :=
  ok (Trusted.btou .U8 b)
def value.convert.trusted.btou_u32 (b : Slice Std.U8) : Result (Option Std.U32) :=
  ok (Trusted.btou .U32 b)

/-! ### regex: opaque, exact on ASCII input, a necessary shape on any input

The seven regexes of `value::convert` (`regex::bytes::Regex`, Unicode mode: `\d` matches any
Unicode decimal digit). On ASCII input `\d` is `[0-9]`, and `^`/`$` anchor at the ends of the
input (`isMatch_ascii`: exact). On any input, a match has the shape of the pattern, where a
`\d` is one ASCII digit or at least two bytes that are all `≥ 128` (`isMatch_loose`: one
direction only; which non-ASCII byte sequences are digits is not specified). -/

namespace Trusted

def digit (b : Std.U8) : Bool := isAsciiDigit b
def byteIn (lo hi : Nat) (b : Std.U8) : Bool := lo ≤ b.val && b.val ≤ hi
def lit (c : Nat) (b : Std.U8) : Bool := b.val = c

/-- The input is exactly one byte per class, in order. -/
def matchSeq : List (Std.U8 → Bool) → List Std.U8 → Bool
  | [], [] => true
  | p :: ps, b :: bs => p b && matchSeq ps bs
  | _, _ => false

/-- `\.\d{1,6}$`. -/
def matchFrac : List Std.U8 → Bool
  | b :: ds => lit 46 b && 1 ≤ ds.length && ds.length ≤ 6 && ds.all isAsciiDigit
  | [] => false

/-- `\d{4}-\d{2}-\d{2}`. -/
def ymd : List (Std.U8 → Bool) :=
  [digit, digit, digit, digit, lit 45, digit, digit, lit 45, digit, digit]
/-- `\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}`. -/
def ymdHms : List (Std.U8 → Bool) :=
  ymd ++ [lit 32, digit, digit, lit 58, digit, digit, lit 58, digit, digit]
/-- `:[0-5]\d:[0-5]\d`. -/
def mmss : List (Std.U8 → Bool) := [lit 58, byteIn 48 53, digit, lit 58, byteIn 48 53, digit]
/-- `\d{2}:[0-5]\d:[0-5]\d`. -/
def hhmmss : List (Std.U8 → Bool) := [digit, digit] ++ mmss
/-- `[0-8]\d\d:[0-5]\d:[0-5]\d`. -/
def hhhmmss : List (Std.U8 → Bool) := [byteIn 48 56, digit, digit] ++ mmss

/-- The regexes of `value::convert`. -/
inductive Regex where
  | datetimeYmd | datetimeYmdHms | datetimeYmdHmsNs
  | timeHhMmSs | timeHhMmSsMs | timeHhhMmSs | timeHhhMmSsMs

/-- What each regex matches, on ASCII input. -/
def Regex.asciiMatch : Regex → List Std.U8 → Bool
  | .datetimeYmd, l => matchSeq ymd l
  | .datetimeYmdHms, l => matchSeq ymdHms l
  | .datetimeYmdHmsNs, l => matchSeq ymdHms (l.take 19) && matchFrac (l.drop 19)
  | .timeHhMmSs, l => matchSeq hhmmss l
  | .timeHhMmSsMs, l => matchSeq hhmmss (l.take 8) && matchFrac (l.drop 8)
  | .timeHhhMmSs, l => matchSeq hhhmmss l
  | .timeHhhMmSsMs, l => matchSeq hhhmmss (l.take 9) && matchFrac (l.drop 9)

/-- `REGEX.is_match(bytes)`: opaque. -/
axiom isMatch : Regex → Slice Std.U8 → Bool

/-- On ASCII input, `is_match` is `Regex.asciiMatch`. -/
axiom isMatch_ascii (r : Regex) (b : Slice Std.U8) (h : ∀ x ∈ b.val, x.val < 128) :
  isMatch r b = r.asciiMatch b.val

/-- One position of a pattern: `\d`, or a class of single bytes `[lo-hi]` (a literal is
    `lo = hi`). Every class of the seven regexes is ASCII (`hi < 128`). -/
inductive Pat where
  | d
  | r (lo hi : Nat)

/-- The shape every match of a pattern has, whatever the input: the input is one piece per
    position, in order, with nothing before, between or after. The piece for a class `[lo-hi]`
    is one byte in that range. The piece for `\d` is one ASCII digit, or at least two bytes
    that are all `≥ 128` (a non-ASCII digit, UTF-8 encoded; nothing more is said about it). -/
def Pat.Loose : List Pat → List Std.U8 → Prop
  | [], l => l = []
  | .r lo hi :: ps, l => ∃ x bs, l = x :: bs ∧ lo ≤ x.val ∧ x.val ≤ hi ∧ Pat.Loose ps bs
  | .d :: ps, l =>
    (∃ x bs, l = x :: bs ∧ isAsciiDigit x = true ∧ Pat.Loose ps bs) ∨
    (∃ u bs, l = u ++ bs ∧ 2 ≤ u.length ∧ (∀ x ∈ u, 128 ≤ x.val) ∧ Pat.Loose ps bs)

/-- `\d{4}-\d{2}-\d{2}`. -/
def Pat.ymd : List Pat := [.d, .d, .d, .d, .r 45 45, .d, .d, .r 45 45, .d, .d]
/-- `\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}`. -/
def Pat.ymdHms : List Pat :=
  Pat.ymd ++ [.r 32 32, .d, .d, .r 58 58, .d, .d, .r 58 58, .d, .d]
/-- `:[0-5]\d:[0-5]\d`. -/
def Pat.mmss : List Pat := [.r 58 58, .r 48 53, .d, .r 58 58, .r 48 53, .d]
/-- `\d{2}:[0-5]\d:[0-5]\d`. -/
def Pat.hhmmss : List Pat := [.d, .d] ++ Pat.mmss
/-- `[0-8]\d\d:[0-5]\d:[0-5]\d`. -/
def Pat.hhhmmss : List Pat := [.r 48 56, .d, .d] ++ Pat.mmss
/-- `\.\d{n}`. -/
def Pat.frac (n : Nat) : List Pat := .r 46 46 :: List.replicate n .d

/-- The shape of a match of each regex (`\.\d{1,6}` is `Pat.frac n` for some `1 ≤ n ≤ 6`). -/
def Regex.Loose : Regex → List Std.U8 → Prop
  | .datetimeYmd, l => Pat.Loose Pat.ymd l
  | .datetimeYmdHms, l => Pat.Loose Pat.ymdHms l
  | .datetimeYmdHmsNs, l => ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Pat.Loose (Pat.ymdHms ++ Pat.frac n) l
  | .timeHhMmSs, l => Pat.Loose Pat.hhmmss l
  | .timeHhMmSsMs, l => ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Pat.Loose (Pat.hhmmss ++ Pat.frac n) l
  | .timeHhhMmSs, l => Pat.Loose Pat.hhhmmss l
  | .timeHhhMmSsMs, l => ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Pat.Loose (Pat.hhhmmss ++ Pat.frac n) l

/-- On any input, a match has the shape of the pattern (`Regex.Loose`). One direction only: it
    says nothing about which inputs with non-ASCII bytes do match.

    Why it is true of regex 1.13.1 (regex-automata 0.4.18, regex-syntax 0.8.11, default
    features, so Unicode mode):
    * the patterns are a concatenation between `^` and `$`, which without the `m` flag are
      `Look::Start`/`Look::End`, the two ends of the haystack
      (regex-syntax `src/hir/translate.rs:924-941`), so the whole input is consumed, one piece
      per position in order;
    * a literal and a bracketed range such as `[0-5]` match exactly one scalar value in that
      range, all below 128, encoded as that single byte;
    * `\d` is the class of scalar values of general category `Nd`
      (`src/hir/translate.rs:398-402`, `1081-1101`; `src/unicode.rs:430-449`, which with the
      default `unicode-gencat` feature uses `general_category::DECIMAL_NUMBER`
      (`src/unicode_tables/general_category.rs`; identical to
      `src/unicode_tables/perl_decimal.rs`): `'0'..='9'`, then nothing below U+0660), compiled to
      the UTF-8 encodings of those scalar values (regex-automata
      `src/nfa/thompson/compiler.rs:1395-1470`, `Utf8Sequences`). So a `\d` matches one ASCII
      digit, or the UTF-8 encoding of a scalar value `≥ U+0660`: two to four bytes, all `≥ 128`.

    Tested (scratch cargo project, regex =1.13.1): `^\d$` against every byte string of length 1,
    2, 3 and every 4-byte string with lead byte `≥ 0xF0` matches exactly the encodings of 760
    scalar values (10 ASCII, 750 from U+0660 up, each 2–4 bytes); each of the 750 at each `\d`
    position of each regex matches, and at each other position does not; and over 43 million
    inputs (34 million with a byte `≥ 128`: pattern instances with digits replaced by Unicode
    digits, other scalar values, truncated and overlong encodings and random high bytes, then
    mutated; plus unstructured strings), 297 thousand of them non-ASCII matches, every match
    had this shape (with blocks of at most 4 bytes) and was valid UTF-8, and on ASCII inputs
    `is_match` equalled `Regex.asciiMatch`. -/
axiom isMatch_loose (r : Regex) (b : Slice Std.U8) (h : isMatch r b = true) : r.Loose b.val

end Trusted

noncomputable def value.convert.trusted.datetime_re_ymd (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .datetimeYmd b)
noncomputable def value.convert.trusted.datetime_re_ymd_hms (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .datetimeYmdHms b)
noncomputable def value.convert.trusted.datetime_re_ymd_hms_ns (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .datetimeYmdHmsNs b)
noncomputable def value.convert.trusted.time_re_hh_mm_ss (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .timeHhMmSs b)
noncomputable def value.convert.trusted.time_re_hh_mm_ss_ms (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .timeHhMmSsMs b)
noncomputable def value.convert.trusted.time_re_hhh_mm_ss (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .timeHhhMmSs b)
noncomputable def value.convert.trusted.time_re_hhh_mm_ss_ms (b : Slice Std.U8) : Result Bool :=
  ok (Trusted.isMatch .timeHhhMmSsMs b)

/-! ### chrono 0.4.45: opaque values; constructors succeed iff the components are valid -/

namespace Trusted

/-- Proleptic Gregorian leap years (chrono's and time's calendar). -/
def isLeapYear (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y : Int) : Nat → Nat
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

/-- `NaiveDate::from_ymd_opt` succeeds: `MIN_YEAR = (i32::MIN >> 13) + 1`,
    `MAX_YEAR = (i32::MAX >> 13) - 1`, and the day exists in that month. -/
def chronoYmdValid (y : Int) (m d : Nat) : Prop :=
  -262143 ≤ y ∧ y ≤ 262142 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m

/-- `NaiveTime::from_hms_micro_opt` succeeds (`micro * 1000` is a valid nanosecond: below
    `2 * 10^9`, and at least `10^9` only for a leap second `sec = 59`). -/
def chronoHmsMicroValid (h m s us : Nat) : Prop :=
  h < 24 ∧ m < 60 ∧ s < 60 ∧ us < 2000000 ∧ (us < 1000000 ∨ s = 59)

axiom NaiveDate.ofYmd : Std.I32 → Std.U32 → Std.U32 → Option chrono.naive.date.NaiveDate
axiom NaiveDate.year : chrono.naive.date.NaiveDate → Std.I32
axiom NaiveDate.month : chrono.naive.date.NaiveDate → Std.U32
axiom NaiveDate.day : chrono.naive.date.NaiveDate → Std.U32
axiom NaiveTime.ofHmsMicro :
  Std.U32 → Std.U32 → Std.U32 → Std.U32 → Option chrono.naive.time.NaiveTime
axiom NaiveTime.hour : chrono.naive.time.NaiveTime → Std.U32
axiom NaiveTime.minute : chrono.naive.time.NaiveTime → Std.U32
axiom NaiveTime.second : chrono.naive.time.NaiveTime → Std.U32
axiom NaiveTime.nanosecond : chrono.naive.time.NaiveTime → Std.U32
axiom NaiveDateTime.new :
  chrono.naive.date.NaiveDate → chrono.naive.time.NaiveTime → chrono.naive.datetime.NaiveDateTime
axiom NaiveDateTime.date : chrono.naive.datetime.NaiveDateTime → chrono.naive.date.NaiveDate
axiom NaiveDateTime.time : chrono.naive.datetime.NaiveDateTime → chrono.naive.time.NaiveTime

axiom NaiveDate.ofYmd_isSome (y : Std.I32) (m d : Std.U32) :
  (NaiveDate.ofYmd y m d).isSome ↔ chronoYmdValid y.val m.val d.val
axiom NaiveDate.ofYmd_some (y : Std.I32) (m d : Std.U32) (x : chrono.naive.date.NaiveDate) :
  NaiveDate.ofYmd y m d = some x → NaiveDate.year x = y ∧ NaiveDate.month x = m ∧ NaiveDate.day x = d
axiom NaiveTime.ofHmsMicro_isSome (h m s us : Std.U32) :
  (NaiveTime.ofHmsMicro h m s us).isSome ↔ chronoHmsMicroValid h.val m.val s.val us.val
axiom NaiveTime.ofHmsMicro_some (h m s us : Std.U32) (x : chrono.naive.time.NaiveTime) :
  NaiveTime.ofHmsMicro h m s us = some x →
    NaiveTime.hour x = h ∧ NaiveTime.minute x = m ∧ NaiveTime.second x = s ∧
      (NaiveTime.nanosecond x).val = us.val * 1000
axiom NaiveDateTime.date_new (d : chrono.naive.date.NaiveDate) (t : chrono.naive.time.NaiveTime) :
  NaiveDateTime.date (NaiveDateTime.new d t) = d
axiom NaiveDateTime.time_new (d : chrono.naive.date.NaiveDate) (t : chrono.naive.time.NaiveTime) :
  NaiveDateTime.time (NaiveDateTime.new d t) = t

end Trusted

noncomputable def value.convert.trusted.naive_date_from_ymd (y : Std.I32) (m d : Std.U32) :
    Result (Option chrono.naive.date.NaiveDate) := ok (Trusted.NaiveDate.ofYmd y m d)
noncomputable def value.convert.trusted.naive_time_from_hms_micro (h m s us : Std.U32) :
    Result (Option chrono.naive.time.NaiveTime) := ok (Trusted.NaiveTime.ofHmsMicro h m s us)
noncomputable def value.convert.trusted.naive_datetime_new (d : chrono.naive.date.NaiveDate)
    (t : chrono.naive.time.NaiveTime) : Result chrono.naive.datetime.NaiveDateTime :=
  ok (Trusted.NaiveDateTime.new d t)
noncomputable def value.convert.trusted.naive_datetime_date
    (x : chrono.naive.datetime.NaiveDateTime) : Result chrono.naive.date.NaiveDate :=
  ok (Trusted.NaiveDateTime.date x)
noncomputable def value.convert.trusted.naive_datetime_time
    (x : chrono.naive.datetime.NaiveDateTime) : Result chrono.naive.time.NaiveTime :=
  ok (Trusted.NaiveDateTime.time x)
noncomputable def value.convert.trusted.naive_date_year (x : chrono.naive.date.NaiveDate) :
    Result Std.I32 := ok (Trusted.NaiveDate.year x)
noncomputable def value.convert.trusted.naive_date_month (x : chrono.naive.date.NaiveDate) :
    Result Std.U32 := ok (Trusted.NaiveDate.month x)
noncomputable def value.convert.trusted.naive_date_day (x : chrono.naive.date.NaiveDate) :
    Result Std.U32 := ok (Trusted.NaiveDate.day x)
noncomputable def value.convert.trusted.naive_time_hour (x : chrono.naive.time.NaiveTime) :
    Result Std.U32 := ok (Trusted.NaiveTime.hour x)
noncomputable def value.convert.trusted.naive_time_minute (x : chrono.naive.time.NaiveTime) :
    Result Std.U32 := ok (Trusted.NaiveTime.minute x)
noncomputable def value.convert.trusted.naive_time_second (x : chrono.naive.time.NaiveTime) :
    Result Std.U32 := ok (Trusted.NaiveTime.second x)
noncomputable def value.convert.trusted.naive_time_nanosecond (x : chrono.naive.time.NaiveTime) :
    Result Std.U32 := ok (Trusted.NaiveTime.nanosecond x)

/-! ### time 0.3.55: `Month` and `Parse` exact; other values opaque

Configuration: time's `large-dates` feature is off (years in `-9999..=9999`). -/

/-- `time::Month::try_from(month).ok()`: exact (`1..=12`). -/
def value.convert.trusted.time_month_from_u8 (m : Std.U8) : Result (Option time.month.Month) :=
  ok (match m.val with
    | 1 => some .January | 2 => some .February | 3 => some .March | 4 => some .April
    | 5 => some .May | 6 => some .June | 7 => some .July | 8 => some .August
    | 9 => some .September | 10 => some .October | 11 => some .November
    | 12 => some .December | _ => none)

/-- `month as u8`: exact (the `#[repr(u8)]` discriminants `1..=12`). -/
def value.convert.trusted.time_month_to_u8 (m : time.month.Month) : Result Std.U8 :=
  ok (match m with
    | .January => 1#u8 | .February => 2#u8 | .March => 3#u8 | .April => 4#u8
    | .May => 5#u8 | .June => 6#u8 | .July => 7#u8 | .August => 8#u8
    | .September => 9#u8 | .October => 10#u8 | .November => 11#u8 | .December => 12#u8)

/-- `Parse::TryFromParsed(TryFromParsed::InsufficientInformation)`: exact. -/
def value.convert.trusted.time_parse_insufficient_information : Result time.error.parse.Parse :=
  ok (.TryFromParsed .InsufficientInformation)

namespace Trusted

def monthNumber (m : time.month.Month) : Nat :=
  match m with
  | .January => 1 | .February => 2 | .March => 3 | .April => 4 | .May => 5 | .June => 6
  | .July => 7 | .August => 8 | .September => 9 | .October => 10 | .November => 11
  | .December => 12

axiom Date.ofCalendarDate : Std.I32 → time.month.Month → Std.U8 → Option time.date.Date
axiom Date.year : time.date.Date → Std.I32
axiom Date.month : time.date.Date → time.month.Month
axiom Date.day : time.date.Date → Std.U8
axiom Time.hour : time.time.Time → Std.U8
axiom Time.minute : time.time.Time → Std.U8
axiom Time.second : time.time.Time → Std.U8
axiom Time.microsecond : time.time.Time → Std.U32
axiom PrimitiveDateTime.new : time.date.Date → time.time.Time → time.plain_date_time.PlainDateTime
axiom PrimitiveDateTime.date : time.plain_date_time.PlainDateTime → time.date.Date
axiom PrimitiveDateTime.time : time.plain_date_time.PlainDateTime → time.time.Time

/-- `Date::from_calendar_date(year, month, day).ok()` succeeds iff `-9999 <= year <= 9999` and the
    day exists in that month; the date then has these components. -/
axiom Date.ofCalendarDate_isSome (y : Std.I32) (m : time.month.Month) (d : Std.U8) :
  (Date.ofCalendarDate y m d).isSome ↔
    (-9999 ≤ y.val ∧ y.val ≤ 9999 ∧ 1 ≤ d.val ∧ d.val ≤ daysInMonth y.val (monthNumber m))
axiom Date.ofCalendarDate_some (y : Std.I32) (m : time.month.Month) (d : Std.U8)
    (x : time.date.Date) :
  Date.ofCalendarDate y m d = some x → Date.year x = y ∧ Date.month x = m ∧ Date.day x = d

/-- `Time::from_hms_micro(h, m, s, us).ok()`. time 0.3.55 checks `hour`, `minute`, `second`
    and then `us * 1000` with `checked_mul` (`ensure_ranged!`, internal_macros.rs:152), so it never
    panics: it is `Ok` iff `h < 24`, `m < 60`, `s < 60` and `us * 1000 < 10^9`, i.e. `us < 10^6`
    (an overflowing multiply also gives `Err`). -/
axiom timeFromHmsMicro :
  Std.U8 → Std.U8 → Std.U8 → Std.U32 → Result (Option time.time.Time)
axiom timeFromHmsMicro_spec (h m s : Std.U8) (us : Std.U32) :
  ∃ r, timeFromHmsMicro h m s us = ok r ∧
    (r.isSome ↔ (h.val < 24 ∧ m.val < 60 ∧ s.val < 60 ∧ us.val < 1000000)) ∧
    ∀ x, r = some x →
      Time.hour x = h ∧ Time.minute x = m ∧ Time.second x = s ∧ Time.microsecond x = us

axiom PrimitiveDateTime.date_new (d : time.date.Date) (t : time.time.Time) :
  PrimitiveDateTime.date (PrimitiveDateTime.new d t) = d
axiom PrimitiveDateTime.time_new (d : time.date.Date) (t : time.time.Time) :
  PrimitiveDateTime.time (PrimitiveDateTime.new d t) = t

/-- The parsers with the format descriptions of `value::convert::time`: opaque. -/
axiom dateParseDate : Str → Option time.date.Date
axiom timeParseTime : Str → core.result.Result time.time.Time time.error.parse.Parse
axiom timeParseTimeMicro : Str → core.result.Result time.time.Time time.error.parse.Parse
/-- The error `PrimitiveDateTime::parse(s, DATE_FORMAT)` returns: opaque (it depends on whether
    the format matched; see `pdtParseDate`). -/
axiom pdtParseDateErr : Str → time.error.parse.Parse
/-- `PrimitiveDateTime::parse(s, DATE_FORMAT)`: always an error, whatever the input. If parsing
    the format fails, that is a parse error; if it succeeds, only a year, month and day have been
    parsed, and time 0.3.55's `TryFrom<Parsed> for Time` needs an hour (parsed.rs:1235-1241, used
    for `PrimitiveDateTime` at parsed.rs:1304), so it is `InsufficientInformation`. Which error is
    left opaque (`pdtParseDateErr`); the caller discards it. (Checked by test in review:
    `"2024-01-31"` is rejected.) -/
noncomputable def pdtParseDate (s : Str) :
    core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse :=
  .Err (pdtParseDateErr s)
axiom pdtParseDateTime :
  Str → core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse
axiom pdtParseDateTimeMicro :
  Str → core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse

/-! #### `time::Duration` (time 0.3.55: `pub type Duration = SignedDuration`, lib.rs:172)

The type stays opaque. It is observed through one getter, `durNanos` (the total nanoseconds), and
each operation the conversions use has one axiom saying exactly when it returns and what the
`durNanos` of its result is. Nothing else is assumed (no extensionality, no surjectivity).

time represents a duration as `seconds: i64` and `nanoseconds` in `-999_999_999..=999_999_999`
(signed_duration.rs:39-40, 50-57) **with the same sign as `seconds`** ("The sign always matches
the `seconds` field", signed_duration.rs:53-54; not a safety invariant, but every public
constructor and operation establishes it, and `new_ranged_unchecked` debug-asserts it,
signed_duration.rs:414-419). `durNanos` is `seconds * 10^9 + nanoseconds`; under that invariant
`seconds = durNanos.tdiv 10^9` and `nanoseconds = durNanos.tmod 10^9` (`Int.tdiv`/`Int.tmod`
truncate toward zero, as Rust's `/` and `%`). The axioms below are time's code read through
these two equations; each one, and the invariant, was checked by a test program against time
0.3.55 (debug build), on `MIN`, `MAX`, ±1 ns around zero, every overflow edge, and random
values, comparing with `whole_nanoseconds()` in `i128`.

The representable range `-2^63 * 10^9 - 999_999_999 ..= (2^63 - 1) * 10^9 + 999_999_999`
(`MIN`, `MAX`: signed_duration.rs:314, 317) is not an axiom: it follows from
`durationWholeSeconds_spec`, whose result is an `i64`. -/

/-- The total number of nanoseconds of a `time::Duration`: `seconds * 10^9 + nanoseconds`
    (= `whole_nanoseconds()`, signed_duration.rs:1033-1035). -/
axiom durNanos : time.signed_duration.SignedDuration → Int

axiom durationDays : Std.I64 → Result time.signed_duration.SignedDuration
axiom durationHours : Std.I64 → Result time.signed_duration.SignedDuration
axiom durationMinutes : Std.I64 → Result time.signed_duration.SignedDuration
axiom durationSeconds : Std.I64 → Result time.signed_duration.SignedDuration
axiom durationMicroseconds : Std.I64 → Result time.signed_duration.SignedDuration
axiom durationAdd : time.signed_duration.SignedDuration → time.signed_duration.SignedDuration →
  Result time.signed_duration.SignedDuration
axiom durationSub : time.signed_duration.SignedDuration → time.signed_duration.SignedDuration →
  Result time.signed_duration.SignedDuration
axiom durationNeg : time.signed_duration.SignedDuration →
  Result time.signed_duration.SignedDuration
axiom durationLtZero : time.signed_duration.SignedDuration → Bool
axiom durationWholeDays : time.signed_duration.SignedDuration → Std.I64
axiom durationWholeHours : time.signed_duration.SignedDuration → Std.I64
axiom durationWholeMinutes : time.signed_duration.SignedDuration → Std.I64
axiom durationWholeSeconds : time.signed_duration.SignedDuration → Std.I64
axiom durationWholeMicroseconds : time.signed_duration.SignedDuration → Std.I128

/-- `Duration::days(x)` is `Self::seconds(x.checked_mul(86_400).expect(..))`
    (signed_duration.rs:521-526): when `x * 86400` fits `i64` it returns that many whole
    seconds. (It panics otherwise; not stated, as no proof needs it.) -/
axiom durationDays_spec (x : Std.I64) :
  -2 ^ 63 ≤ x.val * 86400 ∧ x.val * 86400 < 2 ^ 63 →
    ∃ d, durationDays x = ok d ∧ durNanos d = x.val * 86400 * 10 ^ 9

/-- `Duration::hours(x)` is `Self::seconds(x.checked_mul(3_600).expect(..))`
    (signed_duration.rs:541-547): returns when `x * 3600` fits `i64`. -/
axiom durationHours_spec (x : Std.I64) :
  -2 ^ 63 ≤ x.val * 3600 ∧ x.val * 3600 < 2 ^ 63 →
    ∃ d, durationHours x = ok d ∧ durNanos d = x.val * 3600 * 10 ^ 9

/-- `Duration::minutes(x)` is `Self::seconds(x.checked_mul(60).expect(..))`
    (signed_duration.rs:562-568): returns when `x * 60` fits `i64`. -/
axiom durationMinutes_spec (x : Std.I64) :
  -2 ^ 63 ≤ x.val * 60 ∧ x.val * 60 < 2 ^ 63 →
    ∃ d, durationMinutes x = ok d ∧ durNanos d = x.val * 60 * 10 ^ 9

/-- `Duration::seconds(x)` is `x` seconds and 0 nanoseconds (signed_duration.rs:577-579): it
    never panics. -/
axiom durationSeconds_spec (x : Std.I64) :
  ∃ d, durationSeconds x = ok d ∧ durNanos d = x.val * 10 ^ 9

/-- `Duration::microseconds(x)` is `x / 10^6` seconds and `(x % 10^6) * 1000` nanoseconds
    (signed_duration.rs:814-823; both truncating, so the signs agree and the nanoseconds fit):
    it never panics, and is `x * 1000` nanoseconds. -/
axiom durationMicroseconds_spec (x : Std.I64) :
  ∃ d, durationMicroseconds x = ok d ∧ durNanos d = x.val * 1000

/-- `a + b` is `a.checked_add(b).expect(..)` (signed_duration.rs:1466-1468). `checked_add`
    (signed_duration.rs:1067-1083) adds the seconds (`None` on `i64` overflow) and the
    nanoseconds, then carries one second (`None` on overflow). With equal signs inside `a` and
    inside `b`, either overflow happens only when the true sum is outside the representable
    range: so when the sum is representable it returns the sum. (It panics otherwise; not
    stated.) -/
axiom durationAdd_spec (a b : time.signed_duration.SignedDuration) :
  -2 ^ 63 * 10 ^ 9 - 999999999 ≤ durNanos a + durNanos b ∧
      durNanos a + durNanos b ≤ (2 ^ 63 - 1) * 10 ^ 9 + 999999999 →
    ∃ d, durationAdd a b = ok d ∧ durNanos d = durNanos a + durNanos b

/-- `a - b` is `a.checked_sub(b).expect(..)` (signed_duration.rs:1556-1558). `checked_sub`
    (signed_duration.rs:1096-1112) subtracts the seconds (`None` on `i64` overflow) and the
    nanoseconds, then borrows one second (`None` on overflow). Stated only for
    `0 ≤ b ≤ a`, the only case the conversions use: then both seconds fields are non-negative,
    neither step overflows, and it returns the difference. (In general it also panics when the
    difference is representable but the seconds difference overflows `i64`, e.g.
    `Duration::nanoseconds(-999_999_999) - Duration::seconds(i64::MIN)`; confirmed by test.) -/
axiom durationSub_spec (a b : time.signed_duration.SignedDuration) :
  0 ≤ durNanos b ∧ durNanos b ≤ durNanos a →
    ∃ d, durationSub a b = ok d ∧ durNanos d = durNanos a - durNanos b

/-- `-a` is `a.checked_neg().expect(..)` (signed_duration.rs:1542-1544), and `checked_neg` is
    `None` iff `seconds == i64::MIN`, else both fields negated (signed_duration.rs:1168-1177).
    So it panics iff `a` is at most `-2^63` seconds, which includes `Duration::MIN`, and is
    otherwise the negation. -/
axiom durationNeg_spec (a : time.signed_duration.SignedDuration) :
  (-2 ^ 63 * 10 ^ 9 < durNanos a → ∃ d, durationNeg a = ok d ∧ durNanos d = -durNanos a) ∧
  (durNanos a ≤ -2 ^ 63 * 10 ^ 9 → durationNeg a = fail .panic)

/-- `a < Duration::ZERO`: `Ord` compares the seconds, then the nanoseconds
    (signed_duration.rs:85-91), and `ZERO` is `seconds(0)` (signed_duration.rs:247). -/
axiom durationLtZero_spec (a : time.signed_duration.SignedDuration) :
  durationLtZero a = decide (durNanos a < 0)

/-- `whole_seconds` is the seconds field (signed_duration.rs:937-939), i.e. the nanoseconds
    divided by `10^9`, truncating toward zero. (Stated on every value: it gives the
    representable range.) -/
axiom durationWholeSeconds_spec (a : time.signed_duration.SignedDuration) :
  (durationWholeSeconds a).val = (durNanos a).tdiv (10 ^ 9)

/-- `whole_minutes` is `whole_seconds() / 60` (signed_duration.rs:923-925). Stated only for a
    non-negative duration, where truncating and floor division agree. -/
axiom durationWholeMinutes_spec (a : time.signed_duration.SignedDuration) :
  0 ≤ durNanos a → (durationWholeMinutes a).val = durNanos a / 10 ^ 9 / 60

/-- `whole_hours` is `whole_seconds() / 3_600` (signed_duration.rs:909-911); non-negative
    durations only. -/
axiom durationWholeHours_spec (a : time.signed_duration.SignedDuration) :
  0 ≤ durNanos a → (durationWholeHours a).val = durNanos a / 10 ^ 9 / 3600

/-- `whole_days` is `whole_seconds() / 86_400` (signed_duration.rs:895-897); non-negative
    durations only. -/
axiom durationWholeDays_spec (a : time.signed_duration.SignedDuration) :
  0 ≤ durNanos a → (durationWholeDays a).val = durNanos a / 10 ^ 9 / 86400

/-- `whole_microseconds` is `seconds as i128 * 10^6 + nanoseconds as i128 / 1000`
    (signed_duration.rs:1004-1007), which for a non-negative duration is its nanoseconds
    divided by 1000; non-negative durations only. -/
axiom durationWholeMicroseconds_spec (a : time.signed_duration.SignedDuration) :
  0 ≤ durNanos a → (durationWholeMicroseconds a).val = durNanos a / 1000

end Trusted

noncomputable def value.convert.trusted.time_date_from_calendar_date (y : Std.I32)
    (m : time.month.Month) (d : Std.U8) : Result (Option time.date.Date) :=
  ok (Trusted.Date.ofCalendarDate y m d)
noncomputable def value.convert.trusted.time_time_from_hms_micro (h m s : Std.U8) (us : Std.U32) :
    Result (Option time.time.Time) := Trusted.timeFromHmsMicro h m s us
noncomputable def value.convert.trusted.time_primitive_date_time_new (d : time.date.Date)
    (t : time.time.Time) : Result time.plain_date_time.PlainDateTime :=
  ok (Trusted.PrimitiveDateTime.new d t)
noncomputable def value.convert.trusted.time_primitive_date_time_date
    (x : time.plain_date_time.PlainDateTime) : Result time.date.Date :=
  ok (Trusted.PrimitiveDateTime.date x)
noncomputable def value.convert.trusted.time_primitive_date_time_time
    (x : time.plain_date_time.PlainDateTime) : Result time.time.Time :=
  ok (Trusted.PrimitiveDateTime.time x)
noncomputable def value.convert.trusted.time_date_year (x : time.date.Date) : Result Std.I32 :=
  ok (Trusted.Date.year x)
noncomputable def value.convert.trusted.time_date_month (x : time.date.Date) :
    Result time.month.Month := ok (Trusted.Date.month x)
noncomputable def value.convert.trusted.time_date_day (x : time.date.Date) : Result Std.U8 :=
  ok (Trusted.Date.day x)
noncomputable def value.convert.trusted.time_time_hour (x : time.time.Time) : Result Std.U8 :=
  ok (Trusted.Time.hour x)
noncomputable def value.convert.trusted.time_time_minute (x : time.time.Time) : Result Std.U8 :=
  ok (Trusted.Time.minute x)
noncomputable def value.convert.trusted.time_time_second (x : time.time.Time) : Result Std.U8 :=
  ok (Trusted.Time.second x)
noncomputable def value.convert.trusted.time_time_microsecond (x : time.time.Time) :
    Result Std.U32 := ok (Trusted.Time.microsecond x)
noncomputable def value.convert.trusted.time_date_parse_date (s : Str) :
    Result (Option time.date.Date) := ok (Trusted.dateParseDate s)
noncomputable def value.convert.trusted.time_time_parse_time (s : Str) :
    Result (core.result.Result time.time.Time time.error.parse.Parse) :=
  ok (Trusted.timeParseTime s)
noncomputable def value.convert.trusted.time_time_parse_time_micro (s : Str) :
    Result (core.result.Result time.time.Time time.error.parse.Parse) :=
  ok (Trusted.timeParseTimeMicro s)
noncomputable def value.convert.trusted.time_primitive_date_time_parse_date (s : Str) :
    Result (core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse) :=
  ok (Trusted.pdtParseDate s)
noncomputable def value.convert.trusted.time_primitive_date_time_parse_date_time (s : Str) :
    Result (core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse) :=
  ok (Trusted.pdtParseDateTime s)
noncomputable def value.convert.trusted.time_primitive_date_time_parse_date_time_micro (s : Str) :
    Result (core.result.Result time.plain_date_time.PlainDateTime time.error.parse.Parse) :=
  ok (Trusted.pdtParseDateTimeMicro s)
noncomputable def value.convert.trusted.time_duration_days (x : Std.I64) :
    Result time.signed_duration.SignedDuration := Trusted.durationDays x
noncomputable def value.convert.trusted.time_duration_hours (x : Std.I64) :
    Result time.signed_duration.SignedDuration := Trusted.durationHours x
noncomputable def value.convert.trusted.time_duration_minutes (x : Std.I64) :
    Result time.signed_duration.SignedDuration := Trusted.durationMinutes x
noncomputable def value.convert.trusted.time_duration_seconds (x : Std.I64) :
    Result time.signed_duration.SignedDuration := Trusted.durationSeconds x
noncomputable def value.convert.trusted.time_duration_microseconds (x : Std.I64) :
    Result time.signed_duration.SignedDuration := Trusted.durationMicroseconds x
noncomputable def value.convert.trusted.time_duration_add
    (a b : time.signed_duration.SignedDuration) : Result time.signed_duration.SignedDuration :=
  Trusted.durationAdd a b
noncomputable def value.convert.trusted.time_duration_sub
    (a b : time.signed_duration.SignedDuration) : Result time.signed_duration.SignedDuration :=
  Trusted.durationSub a b
noncomputable def value.convert.trusted.time_duration_neg
    (a : time.signed_duration.SignedDuration) : Result time.signed_duration.SignedDuration :=
  Trusted.durationNeg a
noncomputable def value.convert.trusted.time_duration_lt_zero
    (a : time.signed_duration.SignedDuration) : Result Bool := ok (Trusted.durationLtZero a)
noncomputable def value.convert.trusted.time_duration_whole_days
    (a : time.signed_duration.SignedDuration) : Result Std.I64 := ok (Trusted.durationWholeDays a)
noncomputable def value.convert.trusted.time_duration_whole_hours
    (a : time.signed_duration.SignedDuration) : Result Std.I64 := ok (Trusted.durationWholeHours a)
noncomputable def value.convert.trusted.time_duration_whole_minutes
    (a : time.signed_duration.SignedDuration) : Result Std.I64 :=
  ok (Trusted.durationWholeMinutes a)
noncomputable def value.convert.trusted.time_duration_whole_seconds
    (a : time.signed_duration.SignedDuration) : Result Std.I64 :=
  ok (Trusted.durationWholeSeconds a)
noncomputable def value.convert.trusted.time_duration_whole_microseconds
    (a : time.signed_duration.SignedDuration) : Result Std.I128 :=
  ok (Trusted.durationWholeMicroseconds a)

/-! ### num-bigint 0.5.1, rust_decimal 1.43.0, bigdecimal 0.4.11, serde_json 1.0.154: opaque,
    no specification (only assumed not to panic) -/

namespace Trusted
axiom bigintFromI64 : Std.I64 → num_bigint_1.bigint.BigInt
axiom bigintFromU64 : Std.U64 → num_bigint_1.bigint.BigInt
axiom bigintParseBytes : Slice Std.U8 → Option num_bigint_1.bigint.BigInt
axiom bigintToI64 : num_bigint_1.bigint.BigInt → Option Std.I64
axiom bigintToU64 : num_bigint_1.bigint.BigInt → Option Std.U64
axiom bigintToString : num_bigint_1.bigint.BigInt → String
axiom biguintFromI64 : Std.I64 → Option num_bigint_1.biguint.BigUint
axiom biguintFromU64 : Std.U64 → num_bigint_1.biguint.BigUint
axiom biguintParseBytes : Slice Std.U8 → Option num_bigint_1.biguint.BigUint
axiom biguintToU64 : num_bigint_1.biguint.BigUint → Option Std.U64
axiom biguintToString : num_bigint_1.biguint.BigUint → String
axiom decimalFromI64 : Std.I64 → rust_decimal.decimal.Decimal
axiom decimalFromU64 : Std.U64 → rust_decimal.decimal.Decimal
axiom decimalFromStr : Str → Option rust_decimal.decimal.Decimal
axiom decimalToString : rust_decimal.decimal.Decimal → String
axiom bigdecimalFromI64 : Std.I64 → bigdecimal.BigDecimal
axiom bigdecimalFromU64 : Std.U64 → bigdecimal.BigDecimal
axiom bigdecimalTryFromF32 : F32 → Option bigdecimal.BigDecimal
axiom bigdecimalTryFromF64 : F64 → Option bigdecimal.BigDecimal
axiom bigdecimalParseBytes : Slice Std.U8 → Option bigdecimal.BigDecimal
axiom bigdecimalToString : bigdecimal.BigDecimal → String
axiom jsonFromSlice : Slice Std.U8 → Option serde_json.value.Value
axiom jsonToString : serde_json.value.Value → Option String
end Trusted

noncomputable def value.convert.trusted.bigint_from_i64 (x : Std.I64) :
    Result num_bigint_1.bigint.BigInt := ok (Trusted.bigintFromI64 x)
noncomputable def value.convert.trusted.bigint_from_u64 (x : Std.U64) :
    Result num_bigint_1.bigint.BigInt := ok (Trusted.bigintFromU64 x)
noncomputable def value.convert.trusted.bigint_parse_bytes (b : Slice Std.U8) :
    Result (Option num_bigint_1.bigint.BigInt) := ok (Trusted.bigintParseBytes b)
noncomputable def value.convert.trusted.bigint_to_i64 (x : num_bigint_1.bigint.BigInt) :
    Result (Option Std.I64) := ok (Trusted.bigintToI64 x)
noncomputable def value.convert.trusted.bigint_to_u64 (x : num_bigint_1.bigint.BigInt) :
    Result (Option Std.U64) := ok (Trusted.bigintToU64 x)
noncomputable def value.convert.trusted.bigint_to_string (x : num_bigint_1.bigint.BigInt) :
    Result String := ok (Trusted.bigintToString x)
noncomputable def value.convert.trusted.biguint_from_i64 (x : Std.I64) :
    Result (Option num_bigint_1.biguint.BigUint) := ok (Trusted.biguintFromI64 x)
noncomputable def value.convert.trusted.biguint_from_u64 (x : Std.U64) :
    Result num_bigint_1.biguint.BigUint := ok (Trusted.biguintFromU64 x)
noncomputable def value.convert.trusted.biguint_parse_bytes (b : Slice Std.U8) :
    Result (Option num_bigint_1.biguint.BigUint) := ok (Trusted.biguintParseBytes b)
noncomputable def value.convert.trusted.biguint_to_u64 (x : num_bigint_1.biguint.BigUint) :
    Result (Option Std.U64) := ok (Trusted.biguintToU64 x)
noncomputable def value.convert.trusted.biguint_to_string (x : num_bigint_1.biguint.BigUint) :
    Result String := ok (Trusted.biguintToString x)
noncomputable def value.convert.trusted.decimal_from_i64 (x : Std.I64) :
    Result rust_decimal.decimal.Decimal := ok (Trusted.decimalFromI64 x)
noncomputable def value.convert.trusted.decimal_from_u64 (x : Std.U64) :
    Result rust_decimal.decimal.Decimal := ok (Trusted.decimalFromU64 x)
noncomputable def value.convert.trusted.decimal_from_str (s : Str) :
    Result (Option rust_decimal.decimal.Decimal) := ok (Trusted.decimalFromStr s)
noncomputable def value.convert.trusted.decimal_to_string (x : rust_decimal.decimal.Decimal) :
    Result String := ok (Trusted.decimalToString x)
noncomputable def value.convert.trusted.bigdecimal_from_i64 (x : Std.I64) :
    Result bigdecimal.BigDecimal := ok (Trusted.bigdecimalFromI64 x)
noncomputable def value.convert.trusted.bigdecimal_from_u64 (x : Std.U64) :
    Result bigdecimal.BigDecimal := ok (Trusted.bigdecimalFromU64 x)
noncomputable def value.convert.trusted.bigdecimal_try_from_f32 (x : F32) :
    Result (Option bigdecimal.BigDecimal) := ok (Trusted.bigdecimalTryFromF32 x)
noncomputable def value.convert.trusted.bigdecimal_try_from_f64 (x : F64) :
    Result (Option bigdecimal.BigDecimal) := ok (Trusted.bigdecimalTryFromF64 x)
noncomputable def value.convert.trusted.bigdecimal_parse_bytes (b : Slice Std.U8) :
    Result (Option bigdecimal.BigDecimal) := ok (Trusted.bigdecimalParseBytes b)
noncomputable def value.convert.trusted.bigdecimal_to_string (x : bigdecimal.BigDecimal) :
    Result String := ok (Trusted.bigdecimalToString x)
noncomputable def value.convert.trusted.json_from_slice (b : Slice Std.U8) :
    Result (Option serde_json.value.Value) := ok (Trusted.jsonFromSlice b)
noncomputable def value.convert.trusted.json_to_string (x : serde_json.value.Value) :
    Result (Option String) := ok (Trusted.jsonToString x)

/-! ## `String` / `str` conversions reached by the packets: exact -/

/-- `impl Borrow<str> for String`: the UTF-8 bytes of the string (`Str = Slice U8`). The `fail`
    branch is for a Lean string longer than `usize::MAX` bytes, which no Rust `String` is. -/
@[rust_fun "alloc::str::{core::borrow::Borrow<alloc::string::String, str>}::borrow"]
def alloc.string.String.Insts.CoreBorrowBorrowStr.borrow (s : String) : Result Str :=
  let l := Trusted.u8sOf s.toUTF8
  if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic

/-- `impl ToOwned for str`: the `String` whose UTF-8 bytes are `s`. A Rust `&str` is always valid
    UTF-8; the `fail` branch is only for byte slices that are not, which no `&str` is. -/
@[rust_fun "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned (s : Str) : Result String :=
  match String.fromUTF8? (Trusted.bytesOf s.val) with
  | some x => ok x
  | none => fail .panic

/-! ## Opaque `Display`/`Debug` impls of the packets' error types (opaque in Cargo.toml)

Each formats with `{:b}` or formats a `char`, whose std implementations Aeneas does not model.
They are only needed to build the `Error` instance passed to `io_error_from`, whose result is
opaque. Nothing is assumed about them. -/

axiom constants.UnknownStmtExecuteParamFlags.Insts.CoreFmtDisplay.fmt :
  constants.UnknownStmtExecuteParamFlags → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

axiom constants.UnknownStmtBulkExecuteParamsFlags.Insts.CoreFmtDisplay.fmt :
  constants.UnknownStmtBulkExecuteParamsFlags → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

axiom packets.UnknownBinlogDumpFlags.Insts.CoreFmtDisplay.fmt :
  packets.UnknownBinlogDumpFlags → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

axiom packets.InvalidTag.Insts.CoreFmtDisplay.fmt :
  packets.InvalidTag → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

axiom packets.InvalidTag.Insts.CoreFmtDebug.fmt :
  packets.InvalidTag → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-! ## The trust boundary of the packets: `mysql_common::misc::trusted`

`translation-patches/64-packets-trusted-module.patch` adds this module (later patches add to it);
as for `value::convert::trusted`, each function is one call into a dependency or into a std
function Aeneas does not model, and the module is `opaque` in Cargo.toml. Each function gets:

* an **exact model**: `btoi_u16`;
* an **exact model on valid input, opaque otherwise**: `from_utf8_lossy` (borrowed bytes iff they
  are valid UTF-8; the replaced string is opaque), `sid_tag_from_utf8` (`Ok` of the bytes iff they
  are valid UTF-8; the error is opaque);
* an **opaque value with no specification**: the `GnoInterval` error, the two version regexes, and
  the `HashMap` of connect attributes (`std::collections::HashMap`, an opaque type in
  TypesExternal.lean) and its operations.

Every helper is assumed not to panic (it returns `ok`). -/

namespace Trusted
/-- `String::from_utf8_lossy` of bytes that are not valid UTF-8: opaque. -/
axiom utf8LossyOwned : Slice Std.U8 → String
/-- The `io::Error` of `Sid::deserialize_tagged` for bytes that are not valid UTF-8: opaque. -/
axiom sidTagUtf8Error : Slice Std.U8 → core.io.error.Error
/-- The `io::Error` of `GnoInterval::check_and_new` for `start >= end`: opaque. -/
axiom gnoIntervalOrderError : Std.U64 → Std.U64 → core.io.error.Error
/-- `VERSION_RE.captures` (groups 1–3): opaque. -/
axiom versionReCaptures : Slice Std.U8 → Option (Slice Std.U8 × Slice Std.U8 × Slice Std.U8)
/-- `MARIADB_VERSION_RE.captures` (groups 1–3): opaque. -/
axiom mariadbVersionReCaptures :
  Slice Std.U8 → Option (Slice Std.U8 × Slice Std.U8 × Slice Std.U8)

/-- The connect-attributes map type. -/
abbrev ConnectAttrs : Type :=
  std.collections.hash.map.HashMap (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit)
    (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) std.hash.random.RandomState
    alloc.alloc.Global
/-- A `HashMap<String, String>`. -/
abbrev StringMap : Type :=
  std.collections.hash.map.HashMap String String std.hash.random.RandomState alloc.alloc.Global

/-- `HashMap::new()`: opaque. -/
axiom connectAttrsNew : ConnectAttrs
/-- `HashMap::insert`: opaque. -/
axiom connectAttrsInsert :
  ConnectAttrs → misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit →
    misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit → ConnectAttrs
/-- The entries in iteration order: opaque. -/
axiom connectAttrsEntries : ConnectAttrs → alloc.vec.Vec (Slice Std.U8 × Slice Std.U8)
/-- `HashMap<String, String>` to connect attributes: opaque. -/
axiom connectAttrsFromStrings : StringMap → ConnectAttrs
/-- `into_owned` of every key and value: opaque. -/
axiom connectAttrsIntoOwned : ConnectAttrs → ConnectAttrs
/-- Connect attributes to `HashMap<String, String>` (lossy UTF-8): opaque. -/
axiom connectAttrsToStrings : ConnectAttrs → StringMap
end Trusted

/-- `String::from_utf8_lossy(bytes)`: `Cow::Borrowed(bytes)` exactly when the bytes are valid
    UTF-8 (std returns the input itself then); otherwise an opaque owned string. -/
noncomputable def misc.trusted.from_utf8_lossy (bytes : Slice Std.U8) :
    Result (alloc.borrow.Cow Str String) :=
  ok (if (Trusted.bytesOf bytes.val).IsValidUTF8 then .Borrowed bytes
      else .Owned (Trusted.utf8LossyOwned bytes))

/-- `std::str::from_utf8(tag_bytes)` with an opaque error: `Ok` of the bytes exactly when they
    are valid UTF-8. -/
noncomputable def misc.trusted.sid_tag_from_utf8 (tag_bytes : Slice Std.U8) :
    Result (core.result.Result Str core.io.error.Error) :=
  ok (if (Trusted.bytesOf tag_bytes.val).IsValidUTF8 then .Ok tag_bytes
      else .Err (Trusted.sidTagUtf8Error tag_bytes))

noncomputable def misc.trusted.gno_interval_order_error (start «end» : Std.U64) :
    Result core.io.error.Error := ok (Trusted.gnoIntervalOrderError start «end»)

noncomputable def misc.trusted.version_re_captures (b : Slice Std.U8) :
    Result (Option (Slice Std.U8 × Slice Std.U8 × Slice Std.U8)) :=
  ok (Trusted.versionReCaptures b)

noncomputable def misc.trusted.mariadb_version_re_captures (b : Slice Std.U8) :
    Result (Option (Slice Std.U8 × Slice Std.U8 × Slice Std.U8)) :=
  ok (Trusted.mariadbVersionReCaptures b)

/-- `btoi::btoi::<u16>(b).ok()`: exact (see the btoi section above). -/
def misc.trusted.btoi_u16 (b : Slice Std.U8) : Result (Option Std.U16) :=
  ok (Trusted.btoiUnsigned .U16 b)

noncomputable def misc.trusted.connect_attrs_new : Result Trusted.ConnectAttrs :=
  ok Trusted.connectAttrsNew

noncomputable def misc.trusted.connect_attrs_insert (attrs : Trusted.ConnectAttrs)
    (key value : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    Result Trusted.ConnectAttrs :=
  ok (Trusted.connectAttrsInsert attrs key value)

noncomputable def misc.trusted.connect_attrs_entries (attrs : Trusted.ConnectAttrs) :
    Result (alloc.vec.Vec (Slice Std.U8 × Slice Std.U8)) :=
  ok (Trusted.connectAttrsEntries attrs)

noncomputable def misc.trusted.connect_attrs_from_strings (attrs : Trusted.StringMap) :
    Result Trusted.ConnectAttrs :=
  ok (Trusted.connectAttrsFromStrings attrs)

noncomputable def misc.trusted.connect_attrs_into_owned (attrs : Trusted.ConnectAttrs) :
    Result Trusted.ConnectAttrs :=
  ok (Trusted.connectAttrsIntoOwned attrs)

noncomputable def misc.trusted.connect_attrs_to_strings (attrs : Trusted.ConnectAttrs) :
    Result Trusted.StringMap :=
  ok (Trusted.connectAttrsToStrings attrs)
/-! ## The trust boundary of the compressed codec: `mysql_common::proto::codec::trusted`

`translation-patches/120-codec-trusted-flate2-module.patch` adds this module (opaque in
Cargo.toml); each function is one flate2 operation (flate2 1.1.11 with `rust_backend`, i.e.
miniz_oxide 0.9.1, both checked by `PINNED_DEPS` in
`scripts/aeneas-translate.sh`) or `Vec::capacity`. Each gets one of:

* an **exact model**: `compression_none`, `compression_eq` (`Compression` is its `u32` level,
  see TypesExternal.lean);
* an **opaque value**: the new streams (`compress_new`, which panics for a level above 10,
  `decompress_new`), `Vec::capacity`;
* an **opaque value with partial specification axioms**: `deflate`, `inflate`. The axioms are
  the weakest the codec's round trip needs: a successful deflate is non-empty and shorter than
  its input (`deflateResult_short`), a successful inflate has the declared length
  (`inflateResult_len`, from the helper's body), and inflating a successful deflate gives the
  input back (`inflate_deflate`). Nothing is assumed about errors: deflate may fail, and inflate
  may fail on any input that is not such an output (malformed or wrong length).

Except `compress_new` (above), every helper is assumed not to panic (allocation is infallible in
Aeneas' model). -/

namespace Trusted
/-- `Compress::new(level, true)` (flate2 1.1.11 / miniz_oxide 0.9.1): opaque. -/
axiom compressNew : flate2.Compression → flate2.mem.Compress
/-- `Decompress::new(true)` (flate2 1.1.11 / miniz_oxide 0.9.1): opaque. -/
axiom decompressNew : flate2.mem.Decompress
/-- (flate2 1.1.11 / miniz_oxide 0.9.1.) The result of `trusted::deflate(d, chunk)`: `Ok (Some deflated)`, `Ok None` (incompressible
    or not shorter) or an error. Opaque, see `deflateResult_short` and `inflate_deflate`. -/
axiom deflateResult : flate2.mem.Compress → Slice Std.U8 →
  core.result.Result (Option (alloc.vec.Vec Std.U8)) core.io.error.Error
/-- The stream after `trusted::deflate(d, chunk)` (flate2 1.1.11 / miniz_oxide 0.9.1): opaque. -/
axiom deflateState : flate2.mem.Compress → Slice Std.U8 → flate2.mem.Compress
/-- (flate2 1.1.11 / miniz_oxide 0.9.1.) The result of `trusted::inflate(i, compressed, plain_len)`. Opaque, see `inflateResult_len`
    and `inflate_deflate`. -/
axiom inflateResult : flate2.mem.Decompress → Slice Std.U8 → Std.Usize →
  core.result.Result (alloc.vec.Vec Std.U8) core.io.error.Error
/-- The stream after `trusted::inflate(i, compressed, plain_len)` (flate2 1.1.11 /
    miniz_oxide 0.9.1): opaque. -/
axiom inflateState : flate2.mem.Decompress → Slice Std.U8 → Std.Usize → flate2.mem.Decompress
/-- `Vec::capacity`: opaque (Aeneas does not model capacity). Nothing is assumed about it.
    Caveat: as a Lean function it gives equal vectors equal capacities; it is only used by the
    codec's shrink-on-threshold logic, whose two branches leave the same (empty) buffer. -/
axiom vecCapacity : alloc.vec.Vec Std.U8 → Std.Usize

/-- (flate2 1.1.11 / miniz_oxide 0.9.1.) A successful deflate is non-empty and shorter than its
    input. Shorter: the helper returns `Some` only when `compressed_len < chunk.len()`, truncating
    its `chunk.len()`-byte buffer to `compressed_len`. Non-empty: `Some` needs
    `Status::StreamEnd`, i.e. a complete zlib stream, which has at least 7 bytes: the 2-byte
    header (miniz_oxide 0.9.1 `src/deflate/core.rs:1790-1797`, written since `Compress::new(..,
    true)` selects the zlib format), at least one block, and the 4-byte Adler-32 trailer
    (`core.rs:1877-1880`). -/
axiom deflateResult_short (d : flate2.mem.Compress) (chunk : Slice Std.U8)
    (out : alloc.vec.Vec Std.U8) :
    deflateResult d chunk = .Ok (some out) →
      0 < out.val.length ∧ out.val.length < chunk.val.length

/-- (flate2 1.1.11 / miniz_oxide 0.9.1.) A successful inflate has the declared length: the helper returns `Ok` only when the stream
    ended with `total_out == plain_len`, and the buffer has `plain_len` bytes. -/
axiom inflateResult_len (i : flate2.mem.Decompress) (s : Slice Std.U8) (n : Std.Usize)
    (v : alloc.vec.Vec Std.U8) :
    inflateResult i s n = .Ok v → v.val.length = n.val

/-- (flate2 1.1.11 / miniz_oxide 0.9.1.) zlib round trip: a successful deflate (a complete zlib stream, `FlushCompress::Finish` and
    `Status::StreamEnd`) inflates, with any inflate stream (the helper resets it with a zlib
    header first), into a buffer of the input's length, to exactly the input. Checked by the
    crate's `compressed_roundtrip_reuses_streams` test (lengths 0 to `MAX_PAYLOAD_LEN + 100`,
    compressible and incompressible data). -/
axiom inflate_deflate (d : flate2.mem.Compress) (chunk : Slice Std.U8)
    (out : alloc.vec.Vec Std.U8) (h : deflateResult d chunk = .Ok (some out))
    (i : flate2.mem.Decompress) (s : Slice Std.U8) (hs : s.val = out.val) :
    ∃ v, inflateResult i s (Slice.len chunk) = .Ok v ∧ v.val = chunk.val
end Trusted

/-- `Compression::none()`: exact (`Compression(0)`). -/
def proto.codec.trusted.compression_none : Result flate2.Compression := ok ⟨0#u32⟩

/-- `a == b`: exact (the derived `PartialEq` of `Compression(u32)`). -/
def proto.codec.trusted.compression_eq (a b : flate2.Compression) : Result Bool :=
  ok (a.level.val == b.level.val)

/-- `Compress::new(level, true)`: panics for a level above 10. flate2 1.1.11's miniz_oxide
    backend has `debug_assert!(level.level() <= 10)` (`src/ffi/miniz_oxide.rs:153`), and the
    proofs use debug semantics (overflow checks and debug assertions on, lean/README.md §4);
    otherwise an opaque stream. (The default `zlib` C backend instead panics for a level above 9
    in every profile, `src/ffi/c.rs:376`; that backend is outside the verified configuration.) -/
noncomputable def proto.codec.trusted.compress_new (level : flate2.Compression) :
    Result flate2.mem.Compress :=
  if level.level.val > 10 then fail .panic else ok (Trusted.compressNew level)

noncomputable def proto.codec.trusted.decompress_new : Result flate2.mem.Decompress :=
  ok Trusted.decompressNew

noncomputable def proto.codec.trusted.deflate (d : flate2.mem.Compress) (chunk : Slice Std.U8) :
    Result ((core.result.Result (Option (alloc.vec.Vec Std.U8)) core.io.error.Error) ×
      flate2.mem.Compress) :=
  ok (Trusted.deflateResult d chunk, Trusted.deflateState d chunk)

noncomputable def proto.codec.trusted.inflate (i : flate2.mem.Decompress) (s : Slice Std.U8)
    (n : Std.Usize) :
    Result ((core.result.Result (alloc.vec.Vec Std.U8) core.io.error.Error) ×
      flate2.mem.Decompress) :=
  ok (Trusted.inflateResult i s n, Trusted.inflateState i s n)

noncomputable def proto.codec.trusted.vec_capacity (v : alloc.vec.Vec Std.U8) : Result Std.Usize :=
  ok (Trusted.vecCapacity v)
/-! ## The trust boundary of `Value::as_sql` and `Params`: `mysql_common::sql_trusted`

`translation-patches/80-sql-trusted-module.patch` adds this module (`opaque` in Cargo.toml); each
function is one call into std. Each gets one of:

* an **exact model**: `String::from(&str)`, `extend(chars())` (concatenation), the integer
  `format!`s (decimal, zero-padded to the field width) and `{:02X}`;
* an **opaque value with no specification**: `format!("{}", x)` of `f32`/`f64` (assumed only
  not to panic);
* the `HashMap<Vec<u8>, Value>` of `Params::Named`: an opaque list of entries
  `Trusted.paramsMapEntries` (in the map's iteration order, which is unspecified) with
  distinct keys, and axioms giving the entries after `default`, `insert` and `remove` **up to
  permutation** (`List.Perm`). `contains_key`/`get`/`insert`/`remove`/`into_iter` are then
  definitions in terms of these. A model satisfying all the axioms: a duplicate-free
  association list, with `insert` consing a new key. **Caveat:** in this model a map's
  iteration order is a deterministic function of the operations that built it, while Rust
  seeds every `HashMap` randomly (std `hash/random.rs`), so two maps built the same way may
  iterate differently. Specs must not state facts relating the order (or the Lean equality)
  of separately built maps, or of the same construction in separate calls. The crate's
  results (`into_values`, `into_positional`) do not depend on the order.

Unless a declaration says otherwise, a helper is assumed not to panic (it returns `ok`). -/

namespace Trusted

/-- `n` in decimal, left-padded with `0` to at least `w` characters: Rust's `{:0w}` for an
    unsigned integer (wider numbers are not truncated). -/
def padDec (w n : Nat) : String :=
  let s := toString n
  "".pushn '0' (w - s.length) ++ s

/-- An upper-case hexadecimal digit (`n < 16`). -/
def hexDigitUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `format!("{:02X}", b)` for a byte `b < 256`: exactly two upper-case hex digits. -/
def hexByteUpper (b : Nat) : String :=
  (String.singleton (hexDigitUpper (b / 16))).push (hexDigitUpper (b % 16))

/-- `format!("{}", x)` of an `f32`: opaque. -/
axiom f32Display : F32 → String

/-- `format!("{}", x)` of an `f64`: opaque. -/
axiom f64Display : F64 → String

/-- The map of `Params::Named`. -/
abbrev ParamsMap :=
  std.collections.hash.map.HashMap (alloc.vec.Vec Std.U8) value.Value std.hash.random.RandomState
    alloc.alloc.Global

/-- The entries of a map, in its iteration order. Rust's order is unspecified and depends on the
    map's random seed: the model is only sound if no spec relates the orders (or the Lean
    equality) of separately built maps (see the section docstring). -/
axiom paramsMapEntries : ParamsMap → List (alloc.vec.Vec Std.U8 × value.Value)

/-- A `HashMap` holds each key at most once. -/
axiom paramsMapEntries_keys_nodup (m : ParamsMap) :
  ((paramsMapEntries m).map fun e => e.1.val).Nodup

/-- A `HashMap` has at most `usize::MAX` entries (`HashMap::len` is a `usize`). -/
axiom paramsMapEntries_length (m : ParamsMap) : (paramsMapEntries m).length ≤ Usize.max

/-- `HashMap::default()`. -/
axiom paramsMapEmpty : ParamsMap

/-- `HashMap::default()` has no entries. -/
axiom paramsMapEntries_empty : paramsMapEntries paramsMapEmpty = []

/-- The value of key `k`, if any. -/
noncomputable def paramsMapLookup (m : ParamsMap) (k : List Std.U8) : Option value.Value :=
  ((paramsMapEntries m).find? fun e => e.1.val = k).map (·.2)

/-- The map after `insert(k, v)`. -/
axiom paramsMapInsert : ParamsMap → alloc.vec.Vec Std.U8 → value.Value → ParamsMap

/-- `insert(k, v)` of a key **not already present** adds the entry `(k, v)`; the order is
    unspecified. (Nothing is assumed when `k` is present: the crate only inserts after a
    `contains_key` check, in `From<Vec<(N, V)>> for Params`.) -/
axiom paramsMapEntries_insert (m : ParamsMap) (k : alloc.vec.Vec Std.U8) (v : value.Value)
    (h : paramsMapLookup m k.val = none)
    -- Needed for consistency with `paramsMapEntries_length`: without it, `Usize.max + 1`
    -- inserts of distinct keys would contradict the length bound (a review derived `False`).
    -- A real `HashMap` cannot grow past `usize::MAX` entries.
    (hlen : (paramsMapEntries m).length < Usize.max) :
  (paramsMapEntries (paramsMapInsert m k v)).Perm ((k, v) :: paramsMapEntries m)

/-- The map after `remove(k)`. -/
axiom paramsMapRemove : ParamsMap → List Std.U8 → ParamsMap

/-- `remove(k)` drops the entry of `k` (if any); the order of the others is unspecified. -/
axiom paramsMapEntries_remove (m : ParamsMap) (k : List Std.U8) :
  (paramsMapEntries (paramsMapRemove m k)).Perm
    ((paramsMapEntries m).filter fun e => e.1.val ≠ k)

end Trusted

/-! ### `String` -/

/-- `String::from(s)`: exact (`Str` is the UTF-8 bytes of a Rust `&str`, which are always valid
    UTF-8, so the `fail` branch is unreachable from Rust). -/
def sql_trusted.string_from_str (s : Str) : Result String :=
  match String.fromUTF8? (Trusted.bytesOf s.val) with
  | some t => ok t
  | none => fail .panic

/-- `s.extend(t.chars())`: exact (appends the characters of `t`). -/
def sql_trusted.string_extend_chars (s t : String) : Result String := ok (s ++ t)

/-! ### `format!` -/

/-- `format!("{}", x)` of an `i64`: exact (decimal, with a leading `-` for negative values). -/
def sql_trusted.format_i64 (x : Std.I64) : Result String := ok (toString x.val)

/-- `format!("{}", x)` of a `u64`: exact (decimal). -/
def sql_trusted.format_u64 (x : Std.U64) : Result String := ok (toString x.val)

/-- `format!("{}", x)` of an `f32`: opaque (float formatting is not modelled). -/
noncomputable def sql_trusted.format_f32 (x : F32) : Result String := ok (Trusted.f32Display x)

/-- `format!("{}", x)` of an `f64`: opaque (float formatting is not modelled). -/
noncomputable def sql_trusted.format_f64 (x : F64) : Result String := ok (Trusted.f64Display x)

/-- `format!("'{:04}-{:02}-{:02}'", y, m, d)`: exact. -/
def sql_trusted.format_date (y : Std.U16) (m d : Std.U8) : Result String :=
  ok ("'" ++ Trusted.padDec 4 y.val ++ "-" ++ Trusted.padDec 2 m.val ++ "-" ++
    Trusted.padDec 2 d.val ++ "'")

/-- `format!("'{:04}-{:02}-{:02} {:02}:{:02}:{:02}'", ..)`: exact. -/
def sql_trusted.format_datetime (y : Std.U16) (m d h i s : Std.U8) : Result String :=
  ok ("'" ++ Trusted.padDec 4 y.val ++ "-" ++ Trusted.padDec 2 m.val ++ "-" ++
    Trusted.padDec 2 d.val ++ " " ++ Trusted.padDec 2 h.val ++ ":" ++ Trusted.padDec 2 i.val ++
    ":" ++ Trusted.padDec 2 s.val ++ "'")

/-- `format!("'{:04}-{:02}-{:02} {:02}:{:02}:{:02}.{:06}'", ..)`: exact. -/
def sql_trusted.format_datetime_micros (y : Std.U16) (m d h i s : Std.U8) (us : Std.U32) :
    Result String :=
  ok ("'" ++ Trusted.padDec 4 y.val ++ "-" ++ Trusted.padDec 2 m.val ++ "-" ++
    Trusted.padDec 2 d.val ++ " " ++ Trusted.padDec 2 h.val ++ ":" ++ Trusted.padDec 2 i.val ++
    ":" ++ Trusted.padDec 2 s.val ++ "." ++ Trusted.padDec 6 us.val ++ "'")

/-- `format!("'-{:03}:{:02}:{:02}'", hours, i, s)`: exact. -/
def sql_trusted.format_time_neg (hours : Std.U32) (i s : Std.U8) : Result String :=
  ok ("'-" ++ Trusted.padDec 3 hours.val ++ ":" ++ Trusted.padDec 2 i.val ++ ":" ++
    Trusted.padDec 2 s.val ++ "'")

/-- `format!("'{:03}:{:02}:{:02}'", hours, i, s)`: exact. -/
def sql_trusted.format_time (hours : Std.U32) (i s : Std.U8) : Result String :=
  ok ("'" ++ Trusted.padDec 3 hours.val ++ ":" ++ Trusted.padDec 2 i.val ++ ":" ++
    Trusted.padDec 2 s.val ++ "'")

/-- `format!("'-{:03}:{:02}:{:02}.{:06}'", hours, minutes, seconds, micros)`: exact. -/
def sql_trusted.format_time_micros_neg (hours : Std.U32) (i s : Std.U8) (us : Std.U32) :
    Result String :=
  ok ("'-" ++ Trusted.padDec 3 hours.val ++ ":" ++ Trusted.padDec 2 i.val ++ ":" ++
    Trusted.padDec 2 s.val ++ "." ++ Trusted.padDec 6 us.val ++ "'")

/-- `format!("'{:03}:{:02}:{:02}.{:06}'", hours, minutes, seconds, micros)`: exact. -/
def sql_trusted.format_time_micros (hours : Std.U32) (i s : Std.U8) (us : Std.U32) :
    Result String :=
  ok ("'" ++ Trusted.padDec 3 hours.val ++ ":" ++ Trusted.padDec 2 i.val ++ ":" ++
    Trusted.padDec 2 s.val ++ "." ++ Trusted.padDec 6 us.val ++ "'")

/-- `format!("{:02X}", c)`: exact (two upper-case hex digits). -/
def sql_trusted.format_hex_upper_02 (c : Std.U8) : Result String :=
  ok (Trusted.hexByteUpper c.val)

/-! ### `HashMap<Vec<u8>, Value>` (see `Trusted.paramsMapEntries`) -/

/-- `HashMap::default()`. -/
noncomputable def sql_trusted.params_map_new : Result Trusted.ParamsMap :=
  ok Trusted.paramsMapEmpty

/-- `map.contains_key(key)`. -/
noncomputable def sql_trusted.params_map_contains_key (m : Trusted.ParamsMap)
    (k : Slice Std.U8) : Result Bool :=
  ok (Trusted.paramsMapLookup m k.val).isSome

/-- `map.insert(key, value)`: the previous value of `key`, and the new map. -/
noncomputable def sql_trusted.params_map_insert (m : Trusted.ParamsMap)
    (k : alloc.vec.Vec Std.U8) (v : value.Value) :
    Result (Option value.Value × Trusted.ParamsMap) :=
  ok (Trusted.paramsMapLookup m k.val, Trusted.paramsMapInsert m k v)

/-- `map.get(key)`. -/
noncomputable def sql_trusted.params_map_get (m : Trusted.ParamsMap) (k : Slice Std.U8) :
    Result (Option value.Value) :=
  ok (Trusted.paramsMapLookup m k.val)

/-- `map.remove(key)`: the value of `key` (if any), and the new map. -/
noncomputable def sql_trusted.params_map_remove (m : Trusted.ParamsMap) (k : Slice Std.U8) :
    Result (Option value.Value × Trusted.ParamsMap) :=
  ok (Trusted.paramsMapLookup m k.val, Trusted.paramsMapRemove m k.val)

/-- `map.into_iter().collect()`: the entries, in the map's iteration order. -/
noncomputable def sql_trusted.params_map_into_entries (m : Trusted.ParamsMap) :
    Result (alloc.vec.Vec (alloc.vec.Vec Std.U8 × value.Value)) :=
  ok (alloc.vec.Vec.from (Trusted.paramsMapEntries m) (Trusted.paramsMapEntries_length m))
