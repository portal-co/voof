#!/usr/bin/env bash
# prepare-native.sh — copy volar's checked-in native Lean emission
# (crates/spec/volar-spec-lean/volar_lean_generated.lean, produced upstream
# by `cargo xtask gen-specs`) from the pinned checkout into the
# VolarSpecNative package. extract-check verifies it matches.
set -euo pipefail
cd "$(dirname "$0")/.."
SOURCES_DIR="${VOOF_SOURCES_DIR:-$PWD/.sources}"
SOURCES_DIR="$(cd "$SOURCES_DIR" && pwd -P)"

src="$SOURCES_DIR/volar/crates/spec/volar-spec-lean/volar_lean_generated.lean"
dst="generated/volar-spec-native/VolarSpecNative/Generated.lean"
[ -f "$src" ] || { echo "prepare-native: $src missing (sync first)" >&2; exit 1; }
mkdir -p "$(dirname "$dst")"
cp "$src" "$dst"
echo "prepare-native: $dst"

# the Aeneas↔native bridge theorems (volar_lean_bridge_generated.lean) into
# VolarSpecBridge/Generated.lean, with the import block prepended
bsrc="$SOURCES_DIR/volar/crates/spec/volar-spec-lean/volar_lean_bridge_generated.lean"
bdst="generated/volar-spec-bridge/VolarSpecBridge/Generated.lean"
[ -f "$bsrc" ] || { echo "prepare-native: $bsrc missing (sync first)" >&2; exit 1; }
mkdir -p "$(dirname "$bdst")"
{
  echo "import VolarSpecBridge.Prelude"
  echo "import VolarSpecGarble.Extraction"
  echo
  tail -n +4 "$bsrc"
} > "$bdst"
echo "prepare-native: $bdst"
