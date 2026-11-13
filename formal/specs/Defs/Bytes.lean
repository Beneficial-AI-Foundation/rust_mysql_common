import MysqlCommon

/-!
# Bytes, integers and buffers

The basic vocabulary of the specs: byte lists, little- and big-endian integers, two's complement,
and how to read the contents of the Rust values the specs talk about (`Cow<[T]>`, `io::Result`).

Everything here is plain Lean on `List U8`, `Nat` and `Int`. A byte is Aeneas' `U8` (an 8-bit
bit vector); `b.val : Nat` is its value.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## The target -/

/-- The verified configuration is `x86_64-unknown-linux-gnu`: `usize` has 64 bits. Aeneas leaves
    the width of `usize` open (`System.Platform.numBits`, 32 or 64), so the few statements whose
    truth depends on it (a `u64 as usize` cast must not truncate) take this as a hypothesis. -/
def Target64 : Prop := System.Platform.numBits = 64

/-! ## Making fixed-width integers from numbers (reduction modulo `2^w`) -/

/-- The byte `n mod 256`. -/
def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

/-- `n mod 2^16` as a `u16`. -/
def u16 (n : Nat) : U16 := ⟨BitVec.ofNat 16 n⟩

/-- `n mod 2^32` as a `u32`. -/
def u32 (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩

/-! ## Byte-order encodings -/

/-- The low `k` bytes of `n`, least significant first (little-endian); `n` is reduced mod
    `2^(8k)`. E.g. `leBytes 2 0x0102 = [0x02, 0x01]`. -/
def leBytes : Nat → Nat → List U8
  | 0, _ => []
  | k + 1, n => byte n :: leBytes k (n / 256)

/-- The low `k` bytes of `n`, most significant first (big-endian). -/
def beBytes (k n : Nat) : List U8 := (leBytes k n).reverse

/-- The low `k` bytes of the two's-complement representation of `x` (little-endian): `x` is taken
    mod `2^(8k)`. E.g. `leBytesI 2 (-1) = [0xFF, 0xFF]`. -/
def leBytesI (k : Nat) (x : Int) : List U8 := leBytes k (x % (2 ^ (8 * k) : Int)).toNat

/-- The number whose little-endian bytes are `bs` (first byte least significant). -/
def leNat : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * leNat bs

/-- The number whose big-endian bytes are `bs` (first byte most significant). -/
def beNat (bs : List U8) : Nat := leNat bs.reverse

/-- The signed number with `w`-bit two's-complement bit pattern `n` (`n < 2^w`): bit `w-1` is the
    sign bit. E.g. `toSigned 8 0xFF = -1`, `toSigned 8 0x7F = 127`. -/
def toSigned (w : Nat) (n : Nat) : Int := if n < 2 ^ (w - 1) then n else (n : Int) - 2 ^ w

/-- Reads a `k`-byte little-endian unsigned integer from the front of `bs`: `none` if `bs` has
    fewer than `k` bytes. -/
def readLE (k : Nat) (bs : List U8) : Option (Nat × List U8) :=
  if k ≤ bs.length then some (leNat (bs.take k), bs.drop k) else none

/-! ## Contents of Rust values -/

/-- The elements of a `Cow<'_, [T]>`, whether borrowed or owned. -/
def cowList {T : Type} : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T) → List T
  | .Borrowed s => s.val
  | .Owned v => v.val

/-- The `Ok` value of an `io::Result` (or any `Result`), `none` for an `Err`. Since `io::Error` is
    opaque, the specs never say more about an error than `okPart r = none`. -/
def okPart {T E : Type} : core.result.Result T E → Option T
  | .Ok x => some x
  | .Err _ => none

/-- The prefix of `bs` before its first `0` byte (all of `bs` if it has no `0`). -/
def beforeZero (bs : List U8) : List U8 := bs.takeWhile (fun b => b.val ≠ 0)

end Defs
