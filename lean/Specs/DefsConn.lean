import Proofs.Defs.LemmasConn

/-!
# Facts about the connection-phase definitions (`lean/Defs/Connection.lean`)
    Pure-Lean properties a signer should read: plugin names and normal form; the crate's
    scramble length agrees with the protocol's below 128 and is wrong from 136; the crate's own
    handshake encoding of a 120–127-byte scramble makes its reader panic and of a 128–247-byte one
    is silently misread; the attributes reader
    inverts the encoding; examples of the two version regexes' intended captures and of the
    MySQL nonce. Proofs: `Proofs/Defs/LemmasConn.lean`.

    **Trusted axioms:** none.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ### Lemmas -/

/-- A known plugin's name names it. -/
recall knownPlugin_authPluginName (p : packets.AuthPlugin) (h : isOtherPlugin p = false) :
    knownPlugin (authPluginName p) = some p

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.knownPlugin_authPluginName
/-- The plugin named `n` has the name `n`. -/
recall IsPluginNamed.authPluginName {n : List U8} {r : packets.AuthPlugin} (h : IsPluginNamed n r) : authPluginName r = n

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.IsPluginNamed.authPluginName
/-- `from_bytes` gives the plugin named by the bytes without one trailing `0`, in normal form. -/
recall PluginFromBytes.named {n : List U8} {r : packets.AuthPlugin} (h : PluginFromBytes n r) :
    IsPluginNamed (dropTrailingNul n) r ∧ PluginCanonical r

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.PluginFromBytes.named
/-- The crate's scramble length is the protocol's for a length byte below 128. -/
recall scramble2LenCrate_of_lt (b : Nat) (h : b < 128) : scramble2LenCrate b = scramble2Len b

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.scramble2LenCrate_of_lt
/-- **The crate's scramble length is wrong for a length byte of 136 or more**: 13 instead of `b - 8`. -/
recall scramble2LenCrate_ne (b : Nat) (h1 : 136 ≤ b) (h2 : b < 256) : scramble2LenCrate b = 13 ∧ scramble2Len b = b - 8 ∧ b - 8 ≠ 13

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.scramble2LenCrate_ne
/-- **The crate cannot read its own handshake** with `CLIENT_SECURE_CONNECTION`, `CLIENT_PLUGIN_AUTH` and a scramble of 120–127 bytes: the written length byte `8 + n` is in `128..135`, and the reader panics. -/
recall handshakePanics_handshakeEnc (hs : Handshake) (s : List U8) (tail : List U8) (hv : NoNul hs.serverVersion)
    (hst : statusRead hs.status = some hs.status) (hl : hs.capsLower < 2 ^ 16)
    (hsec : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s)
    (hn : 120 ≤ s.length ∧ s.length ≤ 127) (h1 : hs.scramble1.length = 8) :
    handshakePanics (handshakeEnc hs ++ tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.handshakePanics_handshakeEnc
/-- **The crate misreads its own handshake** with `CLIENT_SECURE_CONNECTION`, `CLIENT_PLUGIN_AUTH` and a scramble of 128–247 bytes, in every build: the written length byte `8 + n` is in `136..255`, there is no panic, and the reader takes only the first 13 scramble bytes (silently; the rest becomes part of the plugin name). -/
recall handshakeEnc_misread (hs : Handshake) (s : List U8) (tail : List U8) (hv : NoNul hs.serverVersion)
    (hst : statusRead hs.status = some hs.status) (hl : hs.capsLower < 2 ^ 16)
    (hsec : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s)
    (hn : 128 ≤ s.length ∧ s.length ≤ 247) (h1 : hs.scramble1.length = 8) :
    136 ≤ handshakeLenByte hs ∧ handshakeLenByte hs < 256 ∧ ¬ handshakePanics (handshakeEnc hs ++ tail) ∧
      (handshakeRead (handshakeEnc hs ++ tail)).1.map (·.scramble2) = some (some (s.take 13))

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.handshakeEnc_misread
/-- The attributes reader inverts `attrsEnc`. -/
recall connectAttrsRead_attrsEnc (kvs : List (List U8 × List U8)) (tail : List U8) (h : (attrsEnc kvs).length < 2 ^ 64) :
    connectAttrsRead (attrsEnc kvs ++ tail) = (some kvs, tail)

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.connectAttrsRead_attrsEnc
/-- An example of `VERSION_RE`: `8.0.32-0ubuntu0.22.04.2` is version 8.0.32. -/
recall versionReMatch_example :
    digitsTriple (versionReMatch (utf8 "8.0.32-0ubuntu0.22.04.2")) = some (8, 0, 32)

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.versionReMatch_example
/-- An example of `MARIADB_VERSION_RE`: `5.5.5-10.6.12-MariaDB-log` is MariaDB 10.6.12 (the `5.5.5-` prefix is skipped); a MySQL version string does not match. -/
recall mariadbVersionReMatch_example :
    digitsTriple (mariadbVersionReMatch (utf8 "5.5.5-10.6.12-MariaDB-log")) = some (10, 6, 12) ∧
      mariadbVersionReMatch (utf8 "8.0.32") = none

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.mariadbVersionReMatch_example
/-- Example: MySQL's own handshake scramble is read as 8 + 12 bytes of nonce (the 13th, a `0`, is dropped). -/
recall handshakeNonce_mysql (s1 s2 : List U8) (h1 : s1.length = 8) (h2 : s2.length = 12) :
    handshakeNonce s1 (some (s2 ++ [byte 0])) = s1 ++ s2

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms Defs.handshakeNonce_mysql
end Defs
