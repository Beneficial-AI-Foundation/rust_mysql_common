#!/usr/bin/env bash
# Translates the verified configuration of mysql_common to Lean with Charon + Aeneas.
#
#  1. checks that .aeneas/ matches the aeneas rev in lakefile.toml;
#  2. copies the crate into .llbc/work/ and applies translation-patches/*.patch in order;
#  3. runs charon on the patched copy (settings: [package.metadata.charon] in Cargo.toml);
#  4. runs aeneas, writing lean/MysqlCommon/ and translation.json.
#
# The proofs hold only for the configuration fixed here.
set -euo pipefail

# ---- Verified configuration -------------------------------------------------------------------
TARGET="x86_64-unknown-linux-gnu"            # 64-bit, little-endian
# The default features with the zlib backend of flate2 swapped for its pure-Rust backend
# (`flate2/zlib` is a C library that does not cross-compile from macOS; compression is out of
# scope, so the verified code is identical), plus the optional value conversions we verify.
FEATURES="derive,flate2/rust_backend,chrono,time,rust_decimal,bigdecimal,frunk"
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
  --exclude '/.lake/' --exclude '/.git' --exclude '/translation-patches/' \
  ./ "$WORK/"
( cd "$WORK" && git init -q . 2>/dev/null || true )
shopt -s nullglob
for patch in "$ROOT"/translation-patches/*.patch; do
  echo "applying $(basename "$patch")"
  if ! git -C "$WORK" apply --whitespace=nowarn "$patch"; then
    echo "error: $(basename "$patch") does not apply; regenerate it against the current code" >&2
    exit 1
  fi
done
shopt -u nullglob

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
