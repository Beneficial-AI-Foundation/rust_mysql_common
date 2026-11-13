-- Hand-written: the external types of the mysql_common translation (from TypesExternal_Template.lean).
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/-! ## Floats

Aeneas prints Rust's `f32`/`f64` as `F32`/`F64` but its Lean library does not define them. We
represent a float by its IEEE-754 bit pattern: the translated code only moves floats around and
converts them from/to bytes (`from_le_bytes`, `from_be_bytes`, `to_bits`), which are exact
operations on the bit pattern. No float arithmetic or comparison is modelled. -/

/-- `f32`, as its bit pattern (`f32::to_bits`). -/
structure F32 where
  bits : Std.U32

/-- `f64`, as its bit pattern (`f64::to_bits`). -/
structure F64 where
  bits : Std.U64

/-! ## Opaque std types -/

/-- [core::io::error::Error]: opaque. Nothing is assumed about it; specs only ever say that a
    function returns `Err _`.
    Source: '/rustc/library/core/src/io/error.rs', lines 87:0-87:16 -/
@[rust_type "core::io::error::Error"]
axiom core.io.error.Error : Type

/-! ## Models of external types -/

/-- [alloc::sync::Arc]: an `Arc<T>` is modelled by the value it points to. The translated code
    only creates (`Arc::new`), clones and dereferences `Arc`s, and calls `Arc::make_mut` (only
    in `Column::with_*`; no `get_mut`, `ptr_eq` or reference counts). Through these operations
    an `Arc<T>` is indistinguishable from a `T`: `make_mut` clones a shared value before
    mutating it, so no other `Arc` observes the change, which is exactly the value semantics.
    Source: '/rustc/library/alloc/src/sync.rs', lines 274:0-277:1 -/
@[rust_type "alloc::sync::Arc"]
abbrev alloc.sync.Arc.{u} (T : Type u) : Type u := T

/-- [bitflags::traits::Flag]: a named flag value; the fields of the `bitflags` 2.x definition.
    Source: 'bitflags-2.13.2/src/traits.rs', lines 15:0-15:18 -/
@[rust_type "bitflags::traits::Flag"]
structure bitflags.traits.Flag (B : Type _) where
  flagName : Str
  flagValue : B

/-- [core::time::Duration]: std's representation, `secs` and `nanos` (std keeps the invariant
    `nanos < 1_000_000_000`; it is not part of this structure, the constructor
    `value.convert.trusted.duration_new` establishes it).
    Source: '/rustc/library/core/src/time.rs' -/
@[rust_type "core::time::Duration"]
structure core.time.Duration where
  secs : Std.U64
  nanos : Std.U32
  /-- std's invariant (`Duration` only exists with `nanos < 10^9`); without it Lean would admit
      Durations Rust cannot build. -/
  nanos_lt : nanos.val < 1000000000

/-! ## Opaque types of the value-conversion dependencies

The value conversions (`src/value/convert/`, `src/value/json/`) only reach these types through
the opaque helpers of `mysql_common::value::convert::trusted` (see `FunsExternal.lean`). Nothing
is assumed about their representation. -/

/-- [chrono::naive::date::NaiveDate]: opaque (chrono 0.4.45). -/
@[rust_type "chrono::naive::date::NaiveDate"]
axiom chrono.naive.date.NaiveDate : Type

/-- [chrono::naive::time::NaiveTime]: opaque (chrono 0.4.45). -/
@[rust_type "chrono::naive::time::NaiveTime"]
axiom chrono.naive.time.NaiveTime : Type

/-- [chrono::naive::datetime::NaiveDateTime]: opaque (chrono 0.4.45). -/
@[rust_type "chrono::naive::datetime::NaiveDateTime"]
axiom chrono.naive.datetime.NaiveDateTime : Type

/-- [time::date::Date]: opaque (time 0.3.55). -/
@[rust_type "time::date::Date"]
axiom time.date.Date : Type

/-- [time::time::Time]: opaque (time 0.3.55). -/
@[rust_type "time::time::Time"]
axiom time.time.Time : Type

/-- [time::plain_date_time::PlainDateTime] (`time::PrimitiveDateTime`): opaque (time 0.3.55). -/
@[rust_type "time::plain_date_time::PlainDateTime"]
axiom time.plain_date_time.PlainDateTime : Type

/-- [time::signed_duration::SignedDuration] (`time::Duration`): opaque (time 0.3.55). -/
@[rust_type "time::signed_duration::SignedDuration"]
axiom time.signed_duration.SignedDuration : Type

/-- [time::error::component_range::ComponentRange]: opaque (time 0.3.55); only occurs inside
    `time::error::Parse`. -/
@[rust_type "time::error::component_range::ComponentRange"]
axiom time.error.component_range.ComponentRange : Type

/-- [num_bigint::bigint::BigInt]: opaque (num-bigint 0.5.1). -/
@[rust_type "num_bigint#1::bigint::BigInt"]
axiom num_bigint_1.bigint.BigInt : Type

/-- [num_bigint::biguint::BigUint]: opaque (num-bigint 0.5.1). -/
@[rust_type "num_bigint#1::biguint::BigUint"]
axiom num_bigint_1.biguint.BigUint : Type

/-- [rust_decimal::decimal::Decimal]: opaque (rust_decimal 1.43.0). -/
@[rust_type "rust_decimal::decimal::Decimal"]
axiom rust_decimal.decimal.Decimal : Type

/-- [bigdecimal::BigDecimal]: opaque (bigdecimal 0.4.11). -/
@[rust_type "bigdecimal::BigDecimal"]
axiom bigdecimal.BigDecimal : Type

/-- [serde_json::value::Value]: opaque (serde_json 1.0.154; `opaque` in Cargo.toml: its
    `Object(Map<String, Value>)` variant nests the type inside an opaque map, which a Lean
    inductive cannot do). -/
@[rust_type "serde_json::value::Value"]
axiom serde_json.value.Value : Type

/-! ## flate2 (the compressed codec)

The compressed codec (`src/proto/codec/mod.rs`) only reaches these types through the opaque
helpers of `mysql_common::proto::codec::trusted` (translation-patches/120, see
`FunsExternal.lean`). -/

/-- [flate2::Compression]: exact (flate2 1.1.11: `pub struct Compression(u32)`, the level). -/
@[rust_type "flate2::Compression"]
structure flate2.Compression where
  level : Std.U32

/-- [flate2::mem::Compress]: a zlib deflate stream; opaque (flate2 1.1.11). -/
@[rust_type "flate2::mem::Compress"]
axiom flate2.mem.Compress : Type

/-- [flate2::mem::Decompress]: a zlib inflate stream; opaque (flate2 1.1.11). -/
@[rust_type "flate2::mem::Decompress"]
axiom flate2.mem.Decompress : Type
/-! ## `HashMap` (the map of `Params::Named`)

`Params` only reaches its `HashMap<Vec<u8>, Value>` through the opaque helpers of
`mysql_common::sql_trusted` (translation-patches/80, 87). The type is opaque here; its contents
are described in `FunsExternal.lean` (`Trusted.paramsMapEntries`). -/

/-- [std::collections::hash::map::HashMap]: opaque. -/
@[rust_type "std::collections::hash::map::HashMap"]
axiom std.collections.hash.map.HashMap (K : Type _) (V : Type _) (S : Type _) (A : Type _) : Type

/-- [std::hash::random::RandomState]: opaque (the hasher of a `HashMap`; never used directly). -/
@[rust_type "std::hash::random::RandomState"]
axiom std.hash.random.RandomState : Type
