#!/usr/bin/env bash
# setup.sh — install pinned tooling: cargo-hax (+ Charon/Aeneas) and elan.
set -euo pipefail
cd "$(dirname "$0")/.."

hax_version="$(awk '
  $0 == "[hax]" { inhax = 1; next }
  /^\[/ { inhax = 0 }
  inhax && $1 == "version" { gsub(/"/, "", $3); print $3; exit }
' toolchain.toml)"

if ! command -v elan >/dev/null; then
  echo "setup: elan not found; install from https://lean-lang.org/install/" >&2
  exit 1
fi

if ! cargo hax --version 2>/dev/null | grep -q "$hax_version"; then
  echo "setup: installing cargo-hax $hax_version"
  cargo install --locked "cargo-hax@$hax_version"
fi

# Charon + Aeneas are downloaded per hax's pins. `tools install` wants a
# crate dir; any workspace member of the pinned sources works — run it after
# sync.sh, or fall back to a scratch crate.
SOURCES_DIR="${VOOF_SOURCES_DIR:-$PWD/.sources}"
if [ -d "$SOURCES_DIR/volar-ir" ]; then
  (cd "$SOURCES_DIR/volar-ir/crates/ir/volar-ir" && cargo hax tools install)
else
  echo "setup: run scripts/sync.sh first, then re-run to pre-install tools"
fi
echo "setup: ok"
