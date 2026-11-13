import Defs

/-! Facts about the connection-phase definitions (`lean/Defs/Connection.lean`) (spec file:
`Specs/DefsConn.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- A known plugin's name names it. -/
theorem knownPlugin_authPluginName (p : packets.AuthPlugin) (h : isOtherPlugin p = false) :
    knownPlugin (authPluginName p) = some p := by
  sorry

/-- The plugin named `n` has the name `n`. -/
theorem IsPluginNamed.authPluginName {n : List U8} {r : packets.AuthPlugin} (h : IsPluginNamed n r) : authPluginName r = n := by
  sorry

/-- `from_bytes` gives the plugin named by the bytes without one trailing `0`, in normal form. -/
theorem PluginFromBytes.named {n : List U8} {r : packets.AuthPlugin} (h : PluginFromBytes n r) :
    IsPluginNamed (dropTrailingNul n) r ∧ PluginCanonical r := by
  sorry

/-- The crate's scramble length is the protocol's for a length byte below 128. -/
theorem scramble2LenCrate_of_lt (b : Nat) (h : b < 128) : scramble2LenCrate b = scramble2Len b := by
  sorry

/-- **The crate's scramble length is wrong for a length byte of 136 or more**: 13 instead of `b - 8`. -/
theorem scramble2LenCrate_ne (b : Nat) (h1 : 136 ≤ b) (h2 : b < 256) : scramble2LenCrate b = 13 ∧ scramble2Len b = b - 8 ∧ b - 8 ≠ 13 := by
  sorry

/-- **The crate cannot read its own handshake** with `CLIENT_SECURE_CONNECTION`, `CLIENT_PLUGIN_AUTH` and a scramble of 120–127 bytes: the written length byte `8 + n` is in `128..135`, and the reader panics. -/
theorem handshakePanics_handshakeEnc (hs : Handshake) (s : List U8) (tail : List U8) (hv : NoNul hs.serverVersion)
    (hst : statusRead hs.status = some hs.status) (hst2 : hs.status < 2 ^ 16) (hl : hs.capsLower < 2 ^ 16)
    (hsec : hasFlag hs.capsLower CLIENT_SECURE_CONNECTION = true)
    (hpa : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true) (hs2 : hs.scramble2 = some s)
    (hn : 120 ≤ s.length ∧ s.length ≤ 127) (h1 : hs.scramble1.length = 8) :
    handshakePanics (handshakeEnc hs ++ tail) := by
  sorry

/-- The attributes reader inverts `attrsEnc`. -/
theorem connectAttrsRead_attrsEnc (kvs : List (List U8 × List U8)) (tail : List U8) (h : (attrsEnc kvs).length < 2 ^ 64) :
    connectAttrsRead (attrsEnc kvs ++ tail) = (some kvs, tail) := by
  sorry

/-- An example of `VERSION_RE`: `8.0.32-0ubuntu0.22.04.2` is version 8.0.32. -/
theorem versionReMatch_example :
    digitsTriple (versionReMatch (utf8 "8.0.32-0ubuntu0.22.04.2")) = some (8, 0, 32) := by
  sorry

/-- An example of `MARIADB_VERSION_RE`: `5.5.5-10.6.12-MariaDB-log` is MariaDB 10.6.12 (the `5.5.5-` prefix is skipped); a MySQL version string does not match. -/
theorem mariadbVersionReMatch_example :
    digitsTriple (mariadbVersionReMatch (utf8 "5.5.5-10.6.12-MariaDB-log")) = some (10, 6, 12) ∧
      mariadbVersionReMatch (utf8 "8.0.32") = none := by
  sorry

/-- Example: MySQL's own handshake scramble is read as 8 + 12 bytes of nonce (the 13th, a `0`, is dropped). -/
theorem handshakeNonce_mysql (s1 s2 : List U8) (h1 : s1.length = 8) (h2 : s2.length = 12) :
    handshakeNonce s1 (some (s2 ++ [byte 0])) = s1 ++ s2 := by
  sorry

end Defs
