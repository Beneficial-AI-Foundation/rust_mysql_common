#!/usr/bin/env bash
# Translates the verified configuration of mysql_common to Lean with Charon + Aeneas.
#
#  1. checks that .aeneas/ matches the aeneas rev in lakefile.toml;
#  2. copies the crate into .llbc/work/ and applies translation-patches/*.patch in the
#     numeric order of their number prefix (so 120-* comes after 60-*);
#  3. runs charon on the patched copy (settings: [package.metadata.charon] in Cargo.toml);
#  4. runs aeneas, writing lean/MysqlCommon/ and translation.json.
#
# The proofs hold only for the configuration fixed here.
set -euo pipefail

# ---- Verified configuration -------------------------------------------------------------------
TARGET="x86_64-unknown-linux-gnu"            # 64-bit, little-endian
# The default features with the zlib backend of flate2 swapped for its pure-Rust backend
# (`flate2/zlib` is a C library that does not cross-compile from macOS), plus the optional value
# conversions we verify. The compressed codec's results (its flate2 axioms in FunsExternal.lean)
# hold for this rust_backend (miniz_oxide) build only, not for the default zlib build.
FEATURES="derive,flate2/rust_backend,chrono,time,rust_decimal,bigdecimal,frunk"
# The flate2 axioms were checked against these versions. `flate2/rust_backend` is only enabled
# here, so Cargo.lock has no miniz_oxide entry and cargo resolves it afresh: the translation
# stops if the resolved versions are not exactly these.
PINNED_DEPS=$'flate2 v1.1.11\nminiz_oxide v0.9.1'
# -----------------------------------------------------------------------------------------------

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

REV="$(awk '/^\[\[require\]\]/{inreq=1; name=""} inreq && /^name *=/{gsub(/[" ]/,"",$0); split($0,a,"="); name=a[2]} inreq && name=="aeneas" && /^rev *=/{gsub(/[" ]/,"",$0); split($0,a,"="); print a[2]; exit}' lakefile.toml)"
if [[ ! -x .aeneas/aeneas || ! -f .aeneas/.rev || "$(cat .aeneas/.rev)" != "$REV" ]]; then
  echo "error: .aeneas/ does not match aeneas $REV; run scripts/aeneas-install.sh" >&2
  exit 1
fi
TOOLCHAIN="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' .aeneas/rust-toolchain)"

# 2. Patched copy of the crate.
WORK="$ROOT/.llbc/work"
mkdir -p "$WORK"
rsync -a --delete \
  --exclude '/target/' --exclude '/lean/' --exclude '/.llbc/' --exclude '/.aeneas/' \
  --exclude '/.lake/' --exclude '/.git' --exclude '/.claude/' --exclude '/translation-patches/' \
  ./ "$WORK/"
( cd "$WORK" && git init -q . 2>/dev/null || true )
shopt -s nullglob
# Numeric order of the leading number, not glob order (which would put 120-* before 13-*).
PATCHES=( "$ROOT"/translation-patches/*.patch )
if (( ${#PATCHES[@]} > 0 )); then
  PATCHES_SORTED="$(for p in "${PATCHES[@]}"; do basename "$p"; done | LC_ALL=C sort -t- -k1,1n)"
else
  PATCHES_SORTED=""
fi
for name in $PATCHES_SORTED; do
  patch="$ROOT/translation-patches/$name"
  echo "applying $(basename "$patch")"
  if ! git -C "$WORK" apply --whitespace=nowarn "$patch"; then
    echo "error: $(basename "$patch") does not apply; regenerate it against the current code" >&2
    exit 1
  fi
done
shopt -u nullglob

# The flate2 backend versions the axioms rely on (see PINNED_DEPS).
RESOLVED_DEPS="$(cd "$WORK" && RUSTUP_TOOLCHAIN="$TOOLCHAIN" cargo tree -q --locked \
  --target "$TARGET" --no-default-features --features "$FEATURES" -e normal --prefix none -f '{p}' \
  | grep -E '^(flate2|miniz_oxide) ' | sed 's/ (\*)$//' | LC_ALL=C sort -u)"
if [[ "$RESOLVED_DEPS" != "$PINNED_DEPS" ]]; then
  echo "error: flate2 backend resolved to" >&2
  echo "$RESOLVED_DEPS" >&2
  echo "expected (FunsExternal.lean's flate2 axioms were checked against):" >&2
  echo "$PINNED_DEPS" >&2
  exit 1
fi

# 3. Charon.
LLBC="$ROOT/.llbc/mysql_common.llbc"
(
  cd "$WORK"
  RUSTUP_TOOLCHAIN="$TOOLCHAIN" PATH="$ROOT/.aeneas:$PATH" \
    "$ROOT/.aeneas/charon" cargo --preset=aeneas --dest-file "$LLBC" \
    -- --target "$TARGET" --no-default-features --features "$FEATURES" --lib
)

# 4. Aeneas.
mkdir -p "$ROOT/lean/MysqlCommon"
"$ROOT/.aeneas/aeneas" -backend lean -split-files -emit-json \
  -dest "$ROOT/lean" -subdir MysqlCommon "$LLBC"
