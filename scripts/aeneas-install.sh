#!/usr/bin/env bash
# Installs the charon + aeneas binaries pinned by the `rev` of the aeneas dependency in
# lakefile.toml into .aeneas/, the Rust nightly charon-driver was built against, and copies the
# matching lean-toolchain. Does nothing if the right version is already installed.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# The Aeneas release tag: the `rev` of the `aeneas` [[require]] block.
REV="$(awk '/^\[\[require\]\]/{inreq=1; name=""} inreq && /^name *=/{gsub(/[" ]/,"",$0); split($0,a,"="); name=a[2]} inreq && name=="aeneas" && /^rev *=/{gsub(/[" ]/,"",$0); split($0,a,"="); print a[2]; exit}' lakefile.toml)"
if [[ -z "$REV" ]]; then
  echo "error: could not read the aeneas rev from lakefile.toml" >&2
  exit 1
fi

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) PLATFORM=linux-x86_64 ;;
  Linux-aarch64 | Linux-arm64) PLATFORM=linux-aarch64 ;;
  Darwin-arm64) PLATFORM=macos-aarch64 ;;
  *) echo "error: unsupported platform $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac

DEST="$ROOT/.aeneas"
if [[ -x "$DEST/aeneas" ]] && [[ -f "$DEST/.rev" ]] && [[ "$(cat "$DEST/.rev")" == "$REV" ]] \
   && "$DEST/aeneas" -version >/dev/null 2>&1; then
  echo "aeneas $REV already installed in .aeneas/"
else
  echo "Downloading aeneas $REV ($PLATFORM)"
  TMP="$(mktemp -d)"
  trap 'rm -rf "$TMP"' EXIT
  URL="https://github.com/AeneasVerif/aeneas/releases/download/$REV/aeneas-$PLATFORM.tar.gz"
  curl -fsSL "$URL" -o "$TMP/bundle.tar.gz"
  rm -rf "$DEST"
  mkdir -p "$DEST"
  tar xzf "$TMP/bundle.tar.gz" -C "$DEST"
  echo "$REV" > "$DEST/.rev"
fi

# The Rust nightly that charon-driver links against, plus the target we translate for.
TOOLCHAIN="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$DEST/rust-toolchain")"
COMPONENTS="$(sed -n 's/^components *= *\[\(.*\)\]/\1/p' "$DEST/rust-toolchain" | tr -d '" ' | tr ',' ' ')"
TARGET="x86_64-unknown-linux-gnu"
if ! rustup run "$TOOLCHAIN" rustc --version >/dev/null 2>&1 \
   || ! rustup target list --installed --toolchain "$TOOLCHAIN" | grep -qx "$TARGET"; then
  # shellcheck disable=SC2086
  rustup toolchain install "$TOOLCHAIN" --profile minimal \
    $(for c in $COMPONENTS; do printf -- '--component %s ' "$c"; done) --target "$TARGET"
fi

# Lean must match the Aeneas Lean library.
cp "$DEST/backends/lean/lean-toolchain" "$ROOT/lean-toolchain"

# The release bundle ships a prebuilt Aeneas Lean library for the same tag; seed lake's copy of
# the package with it so `lake build` doesn't rebuild Aeneas from source.
if [[ -d "$ROOT/.lake/packages/aeneas/backends/lean" ]] \
   && [[ ! -d "$ROOT/.lake/packages/aeneas/backends/lean/.lake/build" ]] \
   && [[ -d "$DEST/backends/lean/.lake/build" ]]; then
  mkdir -p "$ROOT/.lake/packages/aeneas/backends/lean/.lake"
  cp -R "$DEST/backends/lean/.lake/build" "$ROOT/.lake/packages/aeneas/backends/lean/.lake/"
fi

echo "aeneas: $("$DEST/aeneas" -version 2>&1 | head -1)"
echo "rust toolchain: $TOOLCHAIN"
echo "lean toolchain: $(cat "$ROOT/lean-toolchain")"
