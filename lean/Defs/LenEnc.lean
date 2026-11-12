import Defs.Bytes

/-!
# Length-encoded integers and strings

From the MySQL client/server protocol, "Basic Data Types",
<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_dt_integers.html> and
<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_basic_dt_strings.html>:

An integer `n < 2^64` is sent as

| value                  | bytes                           |
|------------------------|---------------------------------|
| `n < 251`              | `n` (1 byte)                    |
| `251 ≤ n < 2^16`       | `0xFC` + 2-byte little-endian   |
| `2^16 ≤ n < 2^24`      | `0xFD` + 3-byte little-endian   |
| `2^24 ≤ n < 2^64`      | `0xFE` + 8-byte little-endian   |

A first byte `0xFB` is not an integer (it is `NULL` in a text-protocol row), nor is `0xFF` (the
first byte of an ERR packet). A length-encoded string is the length as a length-encoded integer,
followed by that many bytes.

The crate's decoders deviate from the protocol on the undefined first bytes: see
`checkedLenencInt`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The length-encoded integer `n` (meant for `n < 2^64`). -/
def lenencInt (n : Nat) : List U8 :=
  if n < 251 then [byte n]
  else if n < 2 ^ 16 then byte 0xFC :: leBytes 2 n
  else if n < 2 ^ 24 then byte 0xFD :: leBytes 3 n
  else byte 0xFE :: leBytes 8 n

/-- The length-encoded string `s`. -/
def lenencStr (s : List U8) : List U8 := lenencInt s.length ++ s

/-- The protocol's decoder for a length-encoded integer at the front of `bs`: the integer and the
    rest of `bs`, or `none` if `bs` is empty, truncated, or starts with `0xFB` or `0xFF`. -/
def lenencIntDecode : List U8 → Option (Nat × List U8)
  | [] => none
  | b :: rest =>
    if b.val < 0xFB then some (b.val, rest)
    else if b.val = 0xFC then readLE 2 rest
    else if b.val = 0xFD then readLE 3 rest
    else if b.val = 0xFE then readLE 8 rest
    else none

/-- What the crate's checked length-encoded-integer reader (`checked_eat_lenenc_int`) returns,
    with what it leaves of the input.

    * It agrees with `lenencIntDecode` whenever that succeeds.
    * **Crate quirk** (documented on `eat_lenenc_int`): a first byte `0xFB` or `0xFF` decodes as `0`,
      consuming just that byte.
    * On failure (empty or truncated input) the result is `none` and the first byte, if any, has
      been consumed. -/
def checkedLenencInt : List U8 → Option Nat × List U8
  | [] => (none, [])
  | b :: rest =>
    if b.val = 0xFB ∨ b.val = 0xFF then (some 0, rest)
    else match lenencIntDecode (b :: rest) with
      | some (n, rest') => (some n, rest')
      | none => (none, rest)

/-- What the crate's checked length-encoded-string reader (`checked_eat_lenenc_str`) returns,
    with what it leaves of the input: the length is read with `checkedLenencInt` (so with its
    quirk); if the length is read but fewer bytes follow, the result is `none` and the length has
    been consumed. -/
def checkedLenencStr (bs : List U8) : Option (List U8) × List U8 :=
  match checkedLenencInt bs with
  | (none, rest) => (none, rest)
  | (some n, rest) => if n ≤ rest.length then (some (rest.take n), rest.drop n) else (none, rest)

/-- A string prefixed by its length as a `k`-byte little-endian integer (`k = 1`: `u8`,
    `k = 4`: `u32`), as the crate's checked readers (`checked_eat_u8_str`, `checked_eat_u32_str`)
    read it: `none` with the input unchanged if fewer than `k` bytes; `none` with the length
    consumed if fewer bytes follow than the length says. -/
def checkedLenPrefixed (k : Nat) (bs : List U8) : Option (List U8) × List U8 :=
  match readLE k bs with
  | none => (none, bs)
  | some (n, rest) => if n ≤ rest.length then (some (rest.take n), rest.drop n) else (none, rest)

end Defs
