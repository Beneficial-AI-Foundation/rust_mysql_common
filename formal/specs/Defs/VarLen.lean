import Defs.Bytes

/-!
# Variable-length unsigned integers

Two unrelated formats that the crate both calls "variable length".

## MySQL serialization library (`misc::read_varlen_uint`, `misc::write_varlen_uint`)

From <https://dev.mysql.com/doc/dev/mysql-server/latest/PageLibsMysqlSerialization.html> and
`get_size_integer_varlen_unsigned` in MySQL's
`libs/mysql/serialization/variable_length_integers.h`: an unsigned 64-bit integer takes `k`
bytes, `1 ≤ k ≤ 9`. For `k ≤ 8` the `k` bytes are a little-endian number whose lowest `k` bits are
`k - 1` ones followed by a zero, and whose remaining `7k` bits hold the value. For `k = 9` the first
byte is `0xFF` and the next 8 bytes are the value, little-endian. So the number of trailing one
bits of the first byte, plus one, is the number of bytes (8 trailing ones: 9 bytes). The encoder
uses the least `k` that fits the value.

## JSONB variable-length integers (`IntRepr for VarLen`, `BytesRepr for VarLen`)

From MySQL's `sql-common/json_binary.cc` (`read_variable_length`, `append_variable_length`): an
unsigned 32-bit length is written in groups of 7 bits, least significant group first, one group per
byte; bit 7 of a byte is set iff another byte follows. A reader accepts at most 5 bytes and rejects
values above `u32::MAX`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Serialization-library varlen integers -/

/-- The number of bytes of the encoding of `n`: the least `k ≤ 8` with `n < 2^(7k)`, else 9. -/
def varlenUintSize (n : Nat) : Nat :=
  match (List.range' 1 8).find? (fun k => n < 2 ^ (7 * k)) with
  | some k => k
  | none => 9

/-- The serialization-library encoding of `n < 2^64`. -/
def varlenUint (n : Nat) : List U8 :=
  let k := varlenUintSize n
  if k = 9 then byte 0xFF :: leBytes 8 n
  else leBytes k (n * 2 ^ k + (2 ^ (k - 1) - 1))

/-- The number of consecutive one bits of the byte `b`, counting up from bit 0 (between 0 and 8). -/
def trailingOnes (b : U8) : Nat := ((List.range 8).takeWhile (fun i => b.val.testBit i)).length

/-- The serialization-library decoder: the value at the front of `bs` and the rest, or `none` if
    `bs` is empty or shorter than its first byte says. (Like the format description, it accepts a
    value written with more bytes than needed.) -/
def varlenUintDecode : List U8 → Option (Nat × List U8)
  | [] => none
  | b :: rest =>
    let t := trailingOnes b
    if t = 8 then readLE 8 rest
    else
      let k := t + 1
      if k ≤ (b :: rest).length then
        some (leNat ((b :: rest).take k) / 2 ^ k, (b :: rest).drop k)
      else none

/-! ## JSONB varlen integers -/

/-- The JSONB variable-length encoding of `n` (7 bits per byte, least significant first, bit 7 set
    on every byte but the last). -/
def jsonbVarLen (n : Nat) : List U8 :=
  if n < 128 then [byte n] else byte (n % 128 + 128) :: jsonbVarLen (n / 128)
termination_by n
decreasing_by omega

/-- The number whose JSONB groups are `bs` (low 7 bits of each byte, least significant first). -/
def base128 : List U8 → Nat
  | [] => 0
  | b :: bs => b.val % 128 + 128 * base128 bs

/-- What the crate's JSONB varlen reader (`IntRepr::deserialize for VarLen`) returns, with what it
    leaves of the input. It reads bytes up to and including the first one with bit 7 clear, at most
    5 bytes:
    * a last byte among the first 5: the value of the groups read, or `none` (error) if it exceeds
      `u32::MAX`;
    * no such byte among the first 5 (5 continuation bytes, or the input ends first): `none`.
    The bytes read are consumed in every case. -/
def jsonbVarLenRead (bs : List U8) : Option Nat × List U8 :=
  match (bs.take 5).findIdx? (fun b => b.val < 128) with
  | none => (none, bs.drop 5)
  | some j =>
    let v := base128 (bs.take (j + 1))
    (if v < 2 ^ 32 then some v else none, bs.drop (j + 1))

/-- A byte string prefixed by its length as a JSONB varlen integer, as the crate's reader
    (`BytesRepr::deserialize for VarLen`) reads it: the length by `jsonbVarLenRead`, then that many
    bytes; `none` with the length consumed if fewer bytes follow. -/
def jsonbVarLenStrRead (bs : List U8) : Option (List U8) × List U8 :=
  match jsonbVarLenRead bs with
  | (none, rest) => (none, rest)
  | (some n, rest) => if n ≤ rest.length then (some (rest.take n), rest.drop n) else (none, rest)

end Defs
