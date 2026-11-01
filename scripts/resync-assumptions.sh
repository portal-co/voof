#!/usr/bin/env bash
# resync-assumptions.sh <scenario> — re-seed an Assumptions file from its
# current template while preserving the curated extension block.
#
# Layout contract: Assumptions/FunsExternal.lean (or TypesExternal.lean) is
#   <template seed, fill-the-holes applied>
#   <EXTENSIONS marker line>
#   <curated extension block>
# The marker is:  -- EXTENSIONS (curated: preserved across resyncs)
# Used when a scenario's include list grows and the template gains axioms
# (hax only seeds Assumptions on first extraction).
set -euo pipefail
cd "$(dirname "$0")/.."
scenario="$1"
file="${2:-FunsExternal}"
pkgdir="generated/$scenario"
pkg="$(basename "$pkgdir")"

tpl="$pkgdir"/*/Extraction/"${file}"_Template.lean
ass="$pkgdir"/*/Assumptions/"${file}".lean
tpl="$(echo $tpl)"; ass="$(echo $ass)"

marker="-- EXTENSIONS (curated: preserved across resyncs)"
if grep -qF -e "$marker" "$ass"; then
  python3 - "$tpl" "$ass" "$marker" <<'PYEOF'
import sys
tpl, ass, marker = sys.argv[1], sys.argv[2], sys.argv[3]
seed = open(tpl).read()
cur = open(ass).read()
idx = cur.index(marker)
ext = cur[idx:]
open(ass, "w").write(seed.rstrip() + "\n\n" + ext)
print("resynced", ass)
PYEOF
else
  cp "$tpl" "$ass"
  echo "seeded $ass (no extension block)"
fi
