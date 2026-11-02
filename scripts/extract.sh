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
SOURCES_DIR="${VOOF_SOURCES_DIR:-$ROOT/.sources}"
SOURCES_DIR="$(cd "$SOURCES_DIR" && pwd -P)"  # physical: see sync.sh

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
  checkout="$SOURCES_DIR/$repo"
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
  # Seed the scratch package from the committed generated/ so hax's
  # create-only-if-missing curation (lakefile.toml, Assumptions/,
  # Verification/, root module) survives regeneration: generated/ is the
  # source of truth for curated files, Extraction/ is always rewritten.
  if [ -d "$ROOT/generated/$scenario" ]; then
    mkdir -p "$cratedir/proofs/$scenario/lean"
    rsync -a "$ROOT/generated/$scenario/" "$cratedir/proofs/$scenario/lean/"
  fi
  (cd "$cratedir" && cargo hax extract "$scenario")
  rm -rf "$ROOT/generated/$scenario"
  mkdir -p "$ROOT/generated"
  rsync -a --exclude '/llbc/' --exclude '/aeneas-error.log' \
    "$cratedir/proofs/$scenario/lean/" "$ROOT/generated/$scenario/"
  rm -rf "$cratedir/proofs" "$cratedir/hax.toml"

  # Post-process curated Assumptions: aeneas seeds Debug::fmt axioms with a
  # borrow back-reference triple, but the core.fmt.Debug model wants a pair.
  python3 - "$ROOT/generated/$scenario" <<'PYEOF'
import re, sys, glob
pat = re.compile(
    r"RustM\s*\(\(\s*core\.result\.Result\s+Unit\s+core\.fmt\.Error\s*\)"
    r"\s*\u00d7\s*core\.fmt\.Formatter\s*\u00d7\s*"
    r"\(\s*core\.fmt\.Formatter\s*\u2192\s*core\.fmt\.Formatter\s*\)\s*\)")
rep = "RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)"
for f in glob.glob(sys.argv[1] + "/*/Assumptions/*.lean"):
    s = open(f).read()
    if pat.search(s):
        open(f, "w").write(pat.sub(rep, s))
PYEOF
done
echo "extract: done"
