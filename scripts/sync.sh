#!/usr/bin/env bash
# sync.sh — materialize pinned source checkouts into .sources/ and generate
# the dedup .cargo/config.toml (see docs/lean-verification-plan.md §3).
#
# Env overrides (local development): VOOF_SRC_VOLAR, VOOF_SRC_VOLAR_IR,
# VOOF_SRC_CIRRUS point at existing checkouts; they are symlinked into
# .sources/ instead of cloning. They MUST be at the sources.toml rev with an
# empty diff, or the CI freshness check will disagree with local output.
#
# VOOF_SOURCES_DIR overrides the checkout root (default <repo>/.sources).
# Use a path outside any ancestor .cargo/config.toml that patches these
# repos (e.g. "$TMPDIR/voof-sources" under portal-hot) to reproduce CI
# faithfully: cargo merges [patch] tables from ALL ancestor configs, and two
# different paths for the same crate is a lockfile collision.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
SOURCES_DIR="${VOOF_SOURCES_DIR:-$ROOT/.sources}"
mkdir -p "$SOURCES_DIR"
# Canonicalize (physical path): cargo canonicalizes some patch paths and not
# others, and mixing /var with /private/var (macOS TMPDIR) produces phantom
# lockfile collisions.
SOURCES_DIR="$(cd "$SOURCES_DIR" && pwd -P)"

repo_field() { # repo_field <name> <field>
  awk -v repo="$1" -v field="$2" '
    $0 == "[repo." repo "]" { inrepo = 1; next }
    /^\[/ { inrepo = 0 }
    inrepo && $1 == field && $2 == "=" { gsub(/"/, "", $3); print $3; exit }
  ' "$ROOT/sources.toml"
}

# sync_one <name> <envvar>
sync_one() {
  local name="$1" envvar="$2" url rev dest override
  url="$(repo_field "$name" url)"
  rev="$(repo_field "$name" rev)"
  dest="$SOURCES_DIR/$name"
  override="${!envvar:-}"
  if [ -n "$override" ]; then
    override="$(cd "$override" && pwd -P)"
    if [ "$(git -C "$override" rev-parse HEAD)" != "$rev" ]; then
      echo "sync: $envvar checkout $override is not at pinned rev $rev" >&2
      exit 1
    fi
    rm -f "$dest"; ln -sfn "$override" "$dest"
    echo "sync: $name -> $override (override)"
    return
  fi
  if [ -d "$dest/.git" ] && [ "$(git -C "$dest" rev-parse HEAD)" = "$rev" ]; then
    echo "sync: $name already at $rev"
    # Restore pristine tracked state: cargo may have rewritten Cargo.lock
    # (e.g. with stale patch paths), which poisons later resolutions.
    git -C "$dest" restore -- .
  else
    rm -rf "$dest"; mkdir -p "$dest"
    git -C "$dest" init -q
    git -C "$dest" remote add origin "$url"
    git -C "$dest" fetch -q --depth 1 origin "$rev"
    git -C "$dest" checkout -q FETCH_HEAD
    echo "sync: $name cloned at $rev"
  fi
  # Member exclusions (scratch checkout only): some members do not resolve
  # from clean git pins because other portal-co repos carry unpublished
  # pre-publish state. Tracked in sources-patches/<repo>.exclude-members.
  local excl="$ROOT/sources-patches/$name.exclude-members"
  if [ -f "$excl" ]; then
    while IFS= read -r member; do
      case "$member" in ''|'#'*) continue ;; esac
      sed -i.bak -e "/\"$(printf '%s' "$member" | sed 's/[\/.&]/\\&/g')\"/d" \
        "$dest/Cargo.toml"
      rm -f "$dest/Cargo.toml.bak"
    done < "$excl"
    echo "sync: $name: applied $(grep -cv '^\s*#\|^\s*$' "$excl") member exclusion(s)"
  fi
}

# workspace_members <checkout> — print workspace member dirs from the root
# Cargo.toml `members = [...]` list (explicit quoted paths, one per line).
workspace_members() {
  awk '
    /^members = \[/ { inmembers = 1; next }
    inmembers && /^\]/ { exit }
    inmembers { gsub(/[",[:space:]]/, ""); if (length) print }
  ' "$1/Cargo.toml"
}

# gen_patch_blocks <repo> — print [patch] blocks covering BOTH URL spellings
# of this repo, mapping every workspace member to its pinned checkout path.
# In-repo [patch] blocks in consumers (volar, cirrus) point at the same
# sibling dirs via relative paths; cargo treats a config patch and a manifest
# patch to the same canonical directory as one patch, so emitting full
# coverage here is both safe and necessary (in-repo blocks are partial).
gen_patch_blocks() {
  local name="$1" url dir m pkg
  url="$(repo_field "$name" url)"
  dir="$(cd "$SOURCES_DIR/$name" && pwd -P)"
  for spelling in "$url" "${url%.git}"; do
    echo "[patch.'$spelling']"
    while IFS= read -r m; do
      pkg="$(grep -m1 '^name *=' "$dir/$m/Cargo.toml" | sed 's/.*"\(.*\)".*/\1/')"
      echo "$pkg = { path = \"$dir/$m\" }"
    done < <(workspace_members "$dir")
    echo
  done
}

mkdir -p "$SOURCES_DIR/.cargo"
# Warn about ancestor configs that also patch these repos: their entries
# merge with the generated ones (cargo walks up from the crate dir).
_confdir="$SOURCES_DIR"
while [ "$_confdir" != "/" ]; do
  _confdir="$(dirname "$_confdir")"
  if [ -f "$_confdir/.cargo/config.toml" ] &&
     grep -q 'github.com/portal-co/volar' "$_confdir/.cargo/config.toml"; then
    echo "sync: WARNING: ancestor config $_confdir/.cargo/config.toml also patches" >&2
    echo "sync: volar repos; cargo merges it with the generated config. Use" >&2
    echo "sync: VOOF_SOURCES_DIR outside this tree, or VOOF_SRC_* overrides" >&2
    echo "sync: pointing at the same checkouts the ancestor config patches to." >&2
  fi
done
sync_one volar VOOF_SRC_VOLAR
sync_one volar-ir VOOF_SRC_VOLAR_IR
sync_one cirrus VOOF_SRC_CIRRUS

{
  echo "# GENERATED by scripts/sync.sh — do not edit."
  echo "# Single-instance dedup patches; see docs/lean-verification-plan.md."
  echo
  gen_patch_blocks volar-ir
  gen_patch_blocks volar
} > "$SOURCES_DIR/.cargo/config.toml"

echo "sync: wrote $SOURCES_DIR/.cargo/config.toml"
