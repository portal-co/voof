#!/usr/bin/env bash
# check-dedup.sh — assert every portal-co crate resolves to exactly one
# instance (the pinned checkout path) across all three workspaces.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"

for repo in volar volar-ir cirrus; do
  cargo metadata --format-version 1 --manifest-path "$ROOT/.sources/$repo/Cargo.toml" \
    > "$ROOT/.sources/metadata-$repo.json"
done

python3 - "$ROOT/.sources" "$ROOT/.sources"/metadata-*.json <<'PY'
import json, os, sys

sources_dir = os.path.realpath(sys.argv[1])
instances = {}  # crate name -> set of manifest dirs
for path in sys.argv[2:]:
    with open(path) as f:
        meta = json.load(f)
    for pkg in meta["packages"]:
        name, src, mdir = pkg["name"], pkg.get("source"), os.path.dirname(pkg["manifest_path"])
        is_portal_git = src and "github.com/portal-co" in src and any(
            r in src for r in ("/volar", "/cirrus"))
        is_pinned_path = os.path.realpath(mdir).startswith(sources_dir + os.sep)
        if is_portal_git or is_pinned_path:
            instances.setdefault(name, set()).add(os.path.realpath(mdir))

bad = False
for name in sorted(instances):
    dirs = instances[name]
    if len(dirs) > 1:
        bad = True
        print(f"dedup: FAIL {name} resolves to {len(dirs)} instances:", file=sys.stderr)
        for d in sorted(dirs):
            print(f"  - {d}", file=sys.stderr)
if bad:
    sys.exit(1)
print(f"dedup: OK ({len(instances)} portal-co crates, one instance each)")
PY
