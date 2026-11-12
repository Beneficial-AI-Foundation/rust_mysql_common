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
    only creates (`Arc::new`), clones and dereferences `Arc`s (no `get_mut`, `make_mut`,
    `ptr_eq` or reference counts), and through these operations an `Arc<T>` is
    indistinguishable from an immutable `T`.
    Source: '/rustc/library/alloc/src/sync.rs', lines 274:0-277:1 -/
@[rust_type "alloc::sync::Arc"]
abbrev alloc.sync.Arc.{u} (T : Type u) : Type u := T

/-- [bitflags::traits::Flag]: a named flag value; the fields of the `bitflags` 2.x definition.
    Source: 'bitflags-2.13.2/src/traits.rs', lines 15:0-15:18 -/
@[rust_type "bitflags::traits::Flag"]
structure bitflags.traits.Flag (B : Type _) where
  flagName : Str
  flagValue : B
