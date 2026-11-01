#!/usr/bin/env bash
# extract.sh [scenario ...] — regenerate the Lean packages for the given
# hax scenarios (default: all hax-configs/*.hax.toml) into generated/.
#
# Each config file is named <scenario>.hax.toml and must contain:
#   repo  = "volar-ir"            # key from sources.toml
#   crate = "volar-ir"            # package name within that workspace
#   [scenario.<ScenarioName>] ... # hax proof scenario (see hax manual)
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"

configs=()
if [ "$#" -gt 0 ]; then
  for s in "$@"; do configs+=("$ROOT/hax-configs/$s.hax.toml"); done
else
  for f in "$ROOT"/hax-configs/*.hax.toml; do configs+=("$f"); done
fi

toml_value() { # toml_value <file> <key>
  awk -v key="$2" '
    $1 == key && $2 == "=" { gsub(/"/, "", $3); print $3; exit }
  ' "$1"
}

for cfg in "${configs[@]}"; do
  [ -f "$cfg" ] || { echo "extract: no such config $cfg" >&2; exit 1; }
  scenario="$(basename "$cfg" .hax.toml)"
  repo="$(toml_value "$cfg" repo)"
  crate="$(toml_value "$cfg" crate)"
  [ -n "$repo" ] && [ -n "$crate" ] || {
    echo "extract: $cfg needs repo= and crate= keys" >&2; exit 1; }

  # Locate the crate directory by package name among workspace members.
  checkout="$ROOT/.sources/$repo"
  cratedir=""
  while IFS= read -r m; do
    if [ -f "$checkout/$m/Cargo.toml" ] &&
       [ "$(grep -m1 '^name *=' "$checkout/$m/Cargo.toml" | sed 's/.*"\(.*\)".*/\1/')" = "$crate" ]; then
      cratedir="$checkout/$m"; break
    fi
  done < <(awk '
    /^members = \[/ { inmembers = 1; next }
    inmembers && /^\]/ { exit }
    inmembers { gsub(/[",[:space:]]/, ""); if (length) print }
  ' "$checkout/Cargo.toml")
  [ -n "$cratedir" ] || { echo "extract: crate $crate not found in $repo" >&2; exit 1; }

  echo "extract: $scenario ($repo/$crate)"
  cp "$cfg" "$cratedir/hax.toml"
  (cd "$cratedir" && cargo hax extract "$scenario")
  rm -rf "$ROOT/generated/$scenario"
  mkdir -p "$ROOT/generated"
  rsync -a "$cratedir/proofs/$scenario/lean/" "$ROOT/generated/$scenario/"
  rm -rf "$cratedir/proofs" "$cratedir/hax.toml"
done
echo "extract: done"
