#!/usr/bin/env bash
# bump.sh <repo> [<rev>|main] — update the pinned rev in sources.toml.
# Resolves branch names via ls-remote. Regenerate afterwards with
# scripts/extract.sh and commit sources.toml + generated/ together.
set -euo pipefail
cd "$(dirname "$0")/.."
[ "$#" -ge 1 ] || { echo "usage: bump.sh <repo> [<rev>|main]" >&2; exit 1; }
repo="$1"; want="${2:-main}"

url="$(awk -v repo="$repo" '
  $0 == "[repo." repo "]" { inrepo = 1; next }
  /^\[/ { inrepo = 0 }
  inrepo && $1 == "url" { gsub(/"/, "", $3); print $3; exit }
' sources.toml)"
[ -n "$url" ] || { echo "bump: unknown repo $repo" >&2; exit 1; }

# A full 40-char lowercase hex string is already a rev; anything else is a
# branch name to resolve.
if ! printf '%s' "$want" | grep -qE '^[0-9a-f]{40}$'; then
  want="$(git ls-remote "$url" "refs/heads/$want" | cut -f1)"
  [ -n "$want" ] || { echo "bump: cannot resolve ref for $repo" >&2; exit 1; }
fi

awk -v repo="$repo" -v rev="$want" '
  $0 == "[repo." repo "]" { inrepo = 1 }
  /^\[/ && $0 != "[repo." repo "]" { inrepo = 0 }
  inrepo && $1 == "rev" { print "rev = \"" rev "\""; inrepo = 0; next }
  { print }
' sources.toml > sources.toml.new
mv sources.toml.new sources.toml
echo "bump: $repo -> $want"
