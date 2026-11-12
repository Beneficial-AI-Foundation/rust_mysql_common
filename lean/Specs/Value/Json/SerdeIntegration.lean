import Proofs.Value.Json.ParseIrJson
import Proofs.Value.Json.FromJson

/-!
# `src/value/json/serde_integration.rs`
    `FromValue for serde_json::Value` and `From<serde_json::Value> for Value`. `serde_json::Value`
    and serde_json's parser and printer are opaque: glue-level statements.

    **Configuration.** As in `Specs/Io.lean` (serde_json 1.0.154).

    **Definitions used.** `Defs/Convert.lean` (`utf8`), `Defs/Value.lean`.

    **Trusted axioms these statements rest on:** `Trusted.jsonFromSlice`, `Trusted.jsonToString`.

    **Not covered.** The impls for `Deserialized<T>` and `Serialized<T>` (excluded from the
    translation: serde's mutually recursive traits, see Cargo.toml); `value/json/mod.rs`.

    **Behaviour to note.** `From<serde_json::Value> for Value` panics if `serde_json::to_string`
    fails (`unwrap`); serde_json never fails on its own `Value`, but that is not assumed.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl FromValue for serde_json::Value` -/

/-- `TryFrom<Value> for ParseIr<serde_json::Value>`: `Bytes` parsed by `serde_json::from_slice`
    (opaque); anything else is an error carrying the value. The original value is kept. -/
recall value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Bytes b =>
        match Trusted.jsonFromSlice (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrValue.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ParseIr<serde_json::Value>>` for `serde_json::Value` is `commit`, for `Value` is
    `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrValue.from_eq (x : serde_json.value.Value) (w : value.Value) :
    serde_json.value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrValue.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrValue.from_eq`

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall serde_json.value.Value.Insts.Mysql_commonValueConvertFromValueParseIrValue.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt serde_json.value.Value.Insts.Mysql_commonValueConvertFromValueParseIrValue v = ok (match v with
      | .Bytes b =>
        match Trusted.jsonFromSlice (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms serde_json.value.Value.Insts.Mysql_commonValueConvertFromValueParseIrValue.from_value_opt_eq`

/-! ### `impl From<serde_json::Value> for Value` -/

/-- `From<serde_json::Value> for Value`: `Bytes` of `serde_json::to_string` (opaque), when that
    succeeds. -/
recall value.Value.Insts.CoreConvertFromValue.from_spec (x : serde_json.value.Value) (s : String) (hs : Trusted.jsonToString x = some s) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromValue.from x ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromValue.from_spec`

/-- **Panic.** `From<serde_json::Value> for Value` panics when `serde_json::to_string` fails
    (`unwrap`). -/
recall value.Value.Insts.CoreConvertFromValue.from_panic (x : serde_json.value.Value) (hs : Trusted.jsonToString x = none) :
    value.Value.Insts.CoreConvertFromValue.from x = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromValue.from_panic`

end mysql_common
