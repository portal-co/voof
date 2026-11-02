#!/usr/bin/env bash
# sources-patches/volar/apply.sh <volar checkout> — voof extraction patch:
# replace volar-spec's lib.rs with the minimal scenario root and install the
# Aeneas-friendly array shim (src/array.rs), redirecting hybrid_array uses
# to it. Applied to the scratch checkout only; never upstream.
# See docs/lean-verification-plan.md §7a (hybrid_array recursion blocker).
set -euo pipefail
checkout="$1"
dir="$(cd "$(dirname "$0")" && pwd)"
spec="$checkout/crates/spec/volar-spec"

cp "$dir/array.rs" "$spec/src/array.rs"
cp "$dir/lib.rs" "$spec/src/lib.rs"

# Only dependency replacements remain here: redirect hybrid_array to the
# shim, and swap `digest::Digest` (whose Output is hardwired to
# hybrid_array::Array) for the patch's SpecDigest trait. Source-level
# Aeneas-compat fixes land upstream in volar main instead (see garble.rs
# history); the SpecDigest::update AsRef signature keeps call sites
# unmodified.
sed -i.bak -E -e 's/hybrid_array/crate::array/g' \
  -e '/^use digest::Digest;$/d' \
  -e 's/D: Digest/D: crate::SpecDigest<N>/g' \
  "$spec/src/garble.rs"
rm -f "$spec/src/garble.rs.bak"
echo "apply.sh: volar-spec trimmed root + array shim installed"
