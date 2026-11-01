#!/usr/bin/env bash
# build-lean.sh [dir ...] — lake build each generated scenario package
# (default: all of generated/*/) and then the root proofs package, if any.
set -euo pipefail
cd "$(dirname "$0")/.."

dirs=("$@")
if [ "$#" -eq 0 ]; then
  dirs=(generated/*/)
fi
for d in "${dirs[@]}"; do
  [ -f "$d/lakefile.toml" ] || continue
  echo "lake: $d"
  (cd "$d" && lake exe cache get && lake build)
done
if [ -f proofs/lakefile.toml ]; then
  echo "lake: proofs/ (root)"
  (cd proofs && lake exe cache get && lake build)
fi
