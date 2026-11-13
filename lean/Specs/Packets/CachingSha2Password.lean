import Proofs.Packets.CachingSha2Password.PublicKeyRequest

/-!
# `src/packets/caching_sha2_password.rs`
    `PublicKeyRequest`: the client's request (`0x02`) for the server's RSA public key in the
    `caching_sha2_password` exchange (the reply is `PublicKeyResponse`, in
    `Specs/Packets/Connection.lean`). Total reader, exact encoding, round trip.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Connection.lean` (`headerRead`), `Defs/Bytes.lean`.

    **Trusted axioms.** None beyond `io::Error`'s.

    **Not covered.** `Debug`/`Clone`/`PartialEq` derives; the `InvalidPublicKeyRequest` error's
    `Display`/`Error` (formatting).

    **Behaviour to note.** The reader checks the header only; bytes after it are left unread.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct PublicKeyRequest and its impls` -/

/-- `new`: the packet (it has no fields besides the header). -/
recall packets.caching_sha2_password.PublicKeyRequest.new_eq :
    packets.caching_sha2_password.PublicKeyRequest.new = ok { __header := () }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.new_eq`

/-- `Default`: `new()`. -/
recall packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default = ok { __header := () }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default_eq`

/-- `MyDeserialize for PublicKeyRequest`: `SIZE` is `None`. -/
recall packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for PublicKeyRequest`: total; the header `0x02` (`headerRead 0x02`); bytes after it are left unread. -/
recall packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0x02 buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for PublicKeyRequest`: appends `0x02`. -/
recall packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.caching_sha2_password.PublicKeyRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0x02] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip. -/
recall packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x02 :: tail) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

end mysql_common
