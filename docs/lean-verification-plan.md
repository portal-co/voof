# Voof: Lean verification plan for volar, volar-ir, and cirrus

Status: draft
Scope: set up this repo (`github.com/portal-co/voof`) as the Lean 4
verification project for three Rust source repos, with generated Lean code
checked in and regenerated in CI.

## 0. TL;DR

`voof` becomes a standalone repo holding:

1. **Pinned source references** to `portal-co/volar`, `portal-co/volar-ir`,
   and `portal-co/cirrus` (a small manifest of repo → git rev).
2. **Extraction configuration** (`hax.toml` proof scenarios, one per
   verified crate/subset).
3. **Checked-in generated Lean** produced by `cargo hax into lean` (whose
   Lean backend drives Charon + Aeneas under the hood — this is what "run
   Aeneas through hax" means in practice), organized as one Lean package per
   scenario, plus a root Lean package that imports them all.
4. **Hand-written proofs** in each package's `Verification/` directory, which
   hax guarantees it will never overwrite.
5. **CI** that (a) regenerates everything from the pinned revs and fails on
   `git diff`, and (b) builds all Lean packages with `lake build`.

End goals (not immediate): remodel the volar/volar-ir IRs in Lean and prove
compiler passes correct; bind the cryptosystems in volar-spec / cirrus zk+MPC
crates to Lean specs of their security properties. The first milestone is
purely mechanical: repos synced, extraction running, generated Lean checked
in and building in CI.

## 1. Goals and non-goals

Goals, in order:

- **G0** — A reproducible pipeline: pinned source revs → hax/Aeneas
  extraction → Lean packages → `lake build`, all in CI, generated output
  committed to this repo.
- **G1** — Steady growth of extracted coverage across the three workspaces,
  tracked per crate.
- **G2** — Hand-written Lean proofs: IR remodeling (semantics for the
  volar-ir / volar-lir / vaffle IRs), pass-correctness theorems (DCE, CSE,
  constant folding in `volar-ir-opt` / `volar-ir-passes`), and proof binding
  of cryptosystems (volar-spec garbled circuits / VOLE-ZK, cirrus Groth16 /
  garbled-circuit backends) against Lean specs.

Non-goals (for now):

- Verifying the *entirety* of any workspace. Many crates are fundamentally
  out of scope for hax/Aeneas (FFI via `inkwell`/`libloading`, the LLVM
  plugin crates, `unsafe` code, interior mutability, async runtimes). We
  extract deliberately chosen subsets.
- Proving panic freedom of extracted code (hax's Lean backend does not give
  this by default; it is a per-function proof obligation later).
- Modifying the source repos in lockstep. Where a `hax-lib` dependency or
  refactor-for-extractability is needed upstream, that lands as its own PR in
  the source repo; voof only bumps its pin.

## 2. Toolchain background and pins

Per the hax Lean manual (<https://hax.cryspen.com/manual/lean/quick_start/>):

- Extraction is invoked **per crate, not per workspace**: `cargo hax into
  lean` inside a crate directory, or `cargo hax extract <scenario>` driven by
  a `hax.toml` next to that crate's `Cargo.toml`.
- The Lean backend uses **Charon** (Rust → LLBC) and **Aeneas** (LLBC →
  Lean); `cargo hax tools install` pre-fetches them, otherwise first use
  downloads them automatically.
- Output is a complete Lean package: `Extraction/` (hax-owned, regenerated),
  `Assumptions/` (seeded once by hax from the Aeneas template for external
  definitions, then ours to curate), `Verification/` (hand-written, never
  touched by hax), plus a `lakefile.toml` and `lean-toolchain` pinned by hax
  to matching versions.
- The documented CI pattern is exactly what we want: `cargo hax extract`
  followed by `git diff --exit-code` for freshness, then `lake build`.

Pinned versions (record exact values in `toolchain.toml` at the repo root;
all CI and local scripts read from there):

| Tool | How pinned | Notes |
| --- | --- | --- |
| hax | `cargo install --locked --git https://github.com/cryspen/hax --rev <rev> hax` | Also fixes the nightly rustc hax needs (its `rust-toolchain.toml`). |
| Charon / Aeneas | Via `cargo hax tools install` of the pinned hax | Do not install Aeneas independently; version drift vs. hax is a common failure. |
| Lean / Lake | `elan`, toolchain from the generated `lean-toolchain` files | hax pins this; we must keep all scenario packages on the *same* toolchain (see Risks). |
| mathlib | `lake exe cache get` per package | Required for CI build times. |

## 3. Source repo synchronization

The three source repos are public `portal-co` GitHub repos, and `voof`
itself is public too — no credentials are needed anywhere in this pipeline.
A root `sources.toml` pins them:

```toml
[repo.volar]
url = "https://github.com/portal-co/volar.git"
rev = "<full sha>"

[repo.volar-ir]
url = "https://github.com/portal-co/volar-ir.git"
rev = "<full sha>"

[repo.cirrus]
url = "https://github.com/portal-co/cirrus.git"
rev = "<full sha>"
```

`scripts/sync.sh` clones/fetches each pinned rev into `.sources/<name>/`
(gitignored). Checkout layout matters: **cirrus's `Cargo.toml` and the local
dev environment rely on sibling-relative `[patch]` entries in a parent
`.cargo/config.toml`** (e.g. volar-spec patched to `../volar/...`). In CI
from clean Git checkouts those parent configs do not exist, so git
dependencies resolve at their committed `Cargo.lock` revs — that is the
configuration we standardize on. Locally, `scripts/sync.sh` accepts
`VOOF_SRC_VOLAR`, `VOOF_SRC_VOLAR_IR`, `VOOF_SRC_CIRRUS` environment
overrides pointing at existing sibling checkouts (matching how these repos
are developed today); per repo policy we **never** add a voof-local
`.cargo/config.toml` that overrides the existing parent config — CI and
local both extract against unpinned-git-dep resolution unless a parent config
already exists.

Bumping a pin is a deliberate act: `scripts/bump.sh <repo> <sha>` edits
`sources.toml`, and CI regenerates + commits the new extraction output on
that PR. A scheduled workflow (weekly) can open "sources bump" PRs
automatically.

### Cross-repo crate deduplication (mandatory)

The three repos form a dependency chain via git dependencies:

- `volar-ir` ← `volar`: ~20 git deps (`volar-ir`, `volar-ir-passes`,
  `volar-lir`, `vaffle`, `volar-c-backend`, …), plus a self-reference
  (`volar-compiler-passes` via git back into `volar` itself).
- `volar` ← `cirrus`: `volar-spec`, `volar-oram` via git.

Left to themselves, each repo's `Cargo.lock` pins a *different rev* of the
downstream repos, so e.g. cirrus would compile against a `volar-spec`
different from the one voof extracted — and proving a cirrus weaver or
interpreter would silently be proving it against a stale model of its
dependencies. We therefore standardize on **one source tree per crate**,
selected by `sources.toml`, enforced with a **generated `.cargo/config.toml`
with `[patch]` entries**:

- `sync.sh` writes `.sources/.cargo/config.toml` (the common parent of the
  three checkouts) with one patch block per source URL, mapping **every**
  crate that any of the three workspaces consumes from that URL to its path
  in the pinned checkout. The crate list is derived mechanically from the
  pinned checkout's workspace members (not hand-maintained), because partial
  patching silently mixes versions of one workspace — the same failure mode
  the local parent config's os-emulation comments warn about.
- Both URL spellings must be patched where both occur: volar references
  `volar-ir-build` via the *un-suffixed* `https://github.com/portal-co/volar-ir`
  while everything else uses `.git`; cargo treats those as distinct sources
  and a patch on one does not cover the other.
- This file is **generated into the scratch checkout root, never committed
  into any source repo**. Locally it merges with the existing parent
  `portal-hot/.cargo/config.toml` (nearer file wins per key): that config
  already patches `volar.git` → `../volar`, so point `VOOF_SRC_*` at those
  same sibling checkouts and keep them at the `sources.toml` revs
  (`git diff` empty) and the two configs agree. Per repo policy we never
  write a conflicting in-repo patch override.
- **Gate:** `scripts/check-dedup.sh` runs `cargo metadata`/`cargo tree`
  across all three workspaces under the generated config and fails if any
  portal-co crate resolves to more than one source instance (path vs. git,
  or two git revs). This runs in CI alongside the freshness check.

Lean-side consequence: exactly one scenario — hence one Lean package —
exists per shared crate (e.g. `volar-spec` is extracted once, from the volar
checkout). Downstream scenarios (cirrus interpreters/weavers that call
`volar-spec`) replace the auto-seeded `Assumptions/` stubs for those items
with a `require` on the shared crate's Lean package; the patch dedup is what
makes that substitution sound, because the extracted model is provably the
same source the downstream crate compiled against.

### CI checkout

Everything is public, so CI uses anonymous `actions/checkout` / `git clone`
for all three sources and plain cargo git-fetch for their (also public)
dependencies such as asm-common/asm-arch/rv-utils. No tokens, no credential
helpers. The `git-fetch-with-cli` setting in the local parent
`.cargo/config.toml` exists only for the host's own git setup; CI can leave
cargo's default fetcher alone.

## 3a. Source-patch policy (post-M0 pivot)

Two kinds of changes are needed to make Rust sources extractable, and they
live in different places:

1. **Source-level Aeneas-compat fixes** (no dependency replacement): nested
   borrows, borrows of temporaries, loops over `&[&T]`, etc. These are valid
   Rust and valid in the spec subset — they land **upstream in the source
   repo's main**, and voof's pin is bumped in lockstep (same PR/round).
   Examples landed in volar main: `action_result_base`'s let-bindings and
   slice-tail recursion (volar@384db226).
2. **Dependency replacements and subset-external constructs**: dependencies
   Aeneas cannot translate (hybrid_array's trait recursion, digest's
   hardwired `hybrid_array::Array` output), or constructs that cannot be
   expressed in the spec subset without them. These stay as voof-side
   patches in `sources-patches/<repo>/` applied to the scratch checkout only
   (currently: volar-spec's trimmed lib.rs root, the `array.rs` Vec-backed
   shim, and the `SpecDigest` trait).

Long-term direction: the spec subset should be *required* to be
Aeneas-valid given valid dependencies — i.e. upstream CI eventually runs the
extraction scenarios itself, and voof patches shrink to true
dependency-substitution cases only. The current volar-spec patch set is the
interim state.

## 3b. The cleaner-representation pipeline (LANDED for garble, M1)

The volar-side generator direction: volar emits a **cleaner
representation** of its specs, and voof proves the generated representation
**equivalent to the extracted spec** in Lean. Status after M1:

- **`volar-compiler/printer_lean.rs`** (upstream): a native Lean 4 printer
  over the spec IR — plain functions, `structure`s, `List`-based arrays,
  explicit `hash` parameters via a `DigestSt` accumulation-state model,
  `Id.run do` for loops/mutation. Unsupported constructs fail generation
  loudly (no silent wrong code). v1 covers the garble subset
  (Eval/Garble/GarbleTable/GlobalSecret + `absorb_args_bases`).
- `cargo xtask gen-specs` emits
  `crates/spec/volar-spec-lean/volar_lean_generated.lean`, freshness-gated
  by volar's existing `check-specs` CI (same as the TS/dyn outputs).
- **voof `generated/volar-spec-native/`**: the `VolarSpecNative` Lake
  package wrapping that file (copied by `scripts/prepare-native.sh` from
  the pinned checkout; extract-check diffs it). Pure Lean core — no
  mathlib/Aeneas dependency, which is the point.
- **First proof landed**: `Eval_open_Garble_share` (open∘share = id under
  the length invariant) in `VolarSpecNative/Verification.lean`.

### M2 work plan (in progress)

Two proof layers, then the bridge:

1. **Aeneas-side specs** (in `VolarSpecGarble/Verification/`, curated —
   hax never touches it): partial-correctness specs in Aeneas's `spec`
   idiom for the shim's `array.Array.from_fn` (via WF induction on
   `n - i` over the extracted `from_fn_loop`, with a stateless-FnMut
   hypothesis `F.call_mut s i = ok (g i, s)`) and for the share/open
   closures (unfolding the index chain array→Vec→Slice→`getElem?`).
   Capstone: `Eval.open (Garble.share g t) g = ok t` on the extracted
   side, given both arrays have the `N.USIZE` length.
2. **Transport** (new package `generated/volar-spec-bridge/`, requires
   both `VolarSpecGarble` and `VolarSpecNative`; curated): list-spine
   transports `array.Array U8 N → List UInt8` (via Aeneas `U8.val` →
   `UInt8.ofNat`), the size transport `typenum ... .USIZE ↦ n`, and the
   commutation theorems `toNative ∘ share_A = share_N ∘ toNative` (etc.)
   for the digest-free fragment. `DigestSt ↔ SpecDigest` correspondence
   is stated for the digest-taking functions (`and_result`,
   `and_via_table`, `absorb_args_bases`): the extracted side takes an
   abstract digest dict; the native side is instantiated with a hash
   function whose spec matches the dict's `finalize`.
3. The native round-trip (M1) then replays on the extracted side as a
   corollary, giving end-to-end: extraction ⟂ native ⟂ proofs.

**M2 status (landed, digest-free fragment):**
- `VolarSpecGarble/Verification/ProofObligations.lean` — Aeneas-side
  specs: `from_fn_loop_spec` (WF induction over the extracted loop;
  stateless-closure hypothesis), `from_fn_spec`, closure specs for
  share/open, `share_spec`/`open_spec`, and `open_share_roundtrip`
  (`open (share g t) g = ok t` on the Aeneas extraction, no sorry).
- `generated/volar-spec-bridge/` (new curated package, requires both):
  `u8ToUInt8`/`arrToNative`/`garbleToNative`/`evalToNative` transports,
  `share_commutes`/`open_commutes`, and `native_roundtrip_via_bridge` —
  the native round-trip *derived* from the extracted spec's verified
  behavior (not re-proven).
- Proof-engineering notes for this Aeneas version are documented in the
  Verification file header (bind-unfold recipe, vecL transparency
  workaround, fully-instantiated rewrites to protect the loop lambda).
- Still open for M2: the digest-taking functions (`and_result`,
  `and_via_table`, `absorb_args_bases`, `to_share`): the extracted side
  takes an abstract `SpecDigest` dict while the native side takes a
  `hash : List UInt8 → List UInt8` — the correspondence is
  `DigestSt.finalize` parts-concatenation vs the dict's `finalize` of the
  folded `update` chain; also `GarbleTable`/`GlobalSecret` and the
  `n / 8` bit-decomposition lemmas (`to_share`). — `VolarSpecNative` (native) ≡
  `VolarSpecGarble` (Aeneas extraction): transport `List` ↔ the Aeneas
  `Slice` model and `DigestSt` ↔ the opaque digest axioms, then replay the
  native proofs on the extracted side (or vice versa). The volar-spec
  sources-patches patch stays until the emitted repr covers the whole
  module set.

## 4. Extraction configuration (hax.toml scenarios)

Each extraction target is a **proof scenario** in a `hax.toml` *managed by
voof but placed next to the source crate's `Cargo.toml` at extraction time*
(sync.sh copies/symlinks it in; the source repos stay clean — this is the one
deviation from the manual's "hax.toml next to Cargo.toml" and is a plain
file copy). Scenario naming: `<repo>__<crate>__<target>`.

Coverage is staged. Stage 1 targets (pure data types + small pure logic,
chosen to be hax-friendly):

| Scenario | Crate | Why first |
| --- | --- | --- |
| `volar-ir__volar-ir__core` | `crates/ir/volar-ir` | Core IR types; basis for IR remodeling proofs. |
| `volar-ir__volar-ir-passes__constfold` | `crates/ir/volar-ir-passes` | Smallest pass-correctness proof target (constant folding), then DCE/CSE. |
| `volar__volar-spec__garble` | `crates/spec/volar-spec` | no_std crypto spec primitives; first crypto proof-binding target. |
| `cirrus__cirrus-core__core` | `crates/cirrus-core` | Shared circuit/boolean-word foundations. |

Stage 2+: `volar-ir-opt` (DCE/CSE), `volar-lir`, `vaffle`, cirrus
garbled-circuit streaming backend, `cirrus-r1cs-backend`. Explicitly
excluded unless refactored: anything touching `inkwell`/`libloading`
(cirrus-llvm*, volar-llvm-*), LLVM plugins, fuzz harnesses, `std::net` /
tokio / rustls crates, `xtask`.

Each scenario starts with a narrow `include = ["crate::module::item"]` list
(the `--start-from` mechanism) rather than whole-crate extraction, because:

- hax/Aeneas reject `unsafe`, interior mutability, and other constructs —
  narrow inclusion keeps one unsupported function from blocking a crate.
- Smaller extraction = faster `lake build` and more tractable proof
  obligations.

Unsupported-but-needed items get `Assumptions/` stubs (hax seeds these once
from the Aeneas template; we then hand-maintain them — this is also where
models of external RustCrypto primitives like `cipher`/`digest` live for
volar-spec).

## 5. Repository layout

```text
voof/
├── sources.toml                # pinned source revs
├── toolchain.toml              # pinned hax rev, expected lean toolchain
├── .sources/                   # gitignored: pinned checkouts + generated
│   │                           #   .cargo/config.toml patch block
├── scripts/                    # sync.sh, extract.sh, bump.sh, build-lean.sh,
│                               # check-dedup.sh
├── hax-configs/                # hax.toml files, mirrored into source crates by sync
│   └── <scenario>.hax.toml
├── generated/                  # CHECKED IN: one Lean package per scenario
│   └── <scenario>/             # = the crate's proofs/<scenario>/lean/ output
│       ├── <Pkg>/
│       │   ├── Extraction/     # hax-owned, regenerated every run
│       │   ├── Assumptions/    # curated stubs (hax seeds once)
│       │   └── Verification/   # hand-written proofs (hax never touches)
│       ├── lakefile.toml
│       └── lean-toolchain
├── proofs/                     # root package: cross-scenario theorems
│   └── Voof.lean               # e.g. IR semantics shared across scenarios
├── lakefile.toml               # root package, `require`s each scenario pkg by path
└── .github/workflows/
    ├── extract-check.yml       # freshness: re-extract, git diff --exit-code
    ├── lake-build.yml          # build all packages
    └── sources-bump.yml        # scheduled pin-bump PRs
```

Rationale for checking in `generated/`: it makes extraction diffs reviewable
in PRs (you *see* what a source change did to the Lean model), lets proof
work proceed without running hax, and matches the freshness-check pattern
volar already uses for `volar_ts_generated.ts` (`git diff --exit-code` after
regeneration).

## 6. CI

Three workflows, all on `ubuntu-latest` with `elan` + the pinned toolchain:

1. **`extract-check.yml`** (on push/PR, and on sources-bump PRs):
   checkout voof → clone the three sources at pinned revs (side by side,
   anonymous) → install pinned hax (`cargo hax tools install`) → `sync.sh`
   generates the dedup `.cargo/config.toml` and `check-dedup.sh` verifies
   single-instance resolution → for each scenario, copy its `hax.toml` into
   the crate and run `cargo hax extract <scenario>` → rsync
   `proofs/<scenario>/lean/` into `generated/<scenario>/` → `git diff
   --exit-code generated/`. Failure = "extraction output stale; re-run
   `scripts/extract.sh` and commit".
2. **`lake-build.yml`**: `lake exe cache get` then `lake build` in each
   scenario package, then the root `proofs/` package. Matrixed per scenario
   so one failing package doesn't mask others; caching via
   `Swatinem/rust-cache`-equivalent for Lake (`~/.elan`, `.lake`).
3. **`sources-bump.yml`** (weekly): fast-forward each pin to the source
   repo's `main`, run extraction, open a PR with the regenerated output.

A green `main` therefore means: generated Lean matches the pinned sources
*and* everything typechecks/proofs compile.

## 7. Local development

- First time: `scripts/setup.sh` (elan, pinned hax, `cargo hax tools
  install` inside a scratch crate).
- Iterate on proofs: open `generated/<scenario>/` in the Lean LSP directly;
  edit only `Verification/` (and curated `Assumptions/`).
- After a source-repo change: `scripts/extract.sh <scenario>` with
  `VOOF_SRC_*` pointing at your local checkouts, then commit the
  `generated/` diff alongside the `sources.toml` bump.
- Note: hax extraction follows whatever `[patch]` resolution cargo sees.
  Keep local checkouts at the `sources.toml` revs (`git diff` empty) and let
  `sync.sh`'s generated config do the dedup, or the CI freshness check will
  disagree with your local output.

## 7a. M0 findings (landed)

M0 shipped with three scenarios — `volar-side`, `volar-ir-common`
(`generated` types, `complexity::generated`, `Stmt` + derived impls), and
`volar-ir-core` (the `ir` module) — extracted by cargo-hax 0.4.2 and
building green. Findings that shape later milestones:

- **Aeneas closure/region limits**: iterator-closure methods
  (`IRTerminator::as_ref`/`as_mut`/`map`) fail with "Can't end abstraction";
  they are `opaque` (signature-only axioms) for now.
- **Non-positive recursion**: `MeasureSpec` recurses through `Vec`, which
  the Lean kernel rejects; it is an opaque abstract type in Assumptions
  until a mutual-inductive model is written.
- **hax 0.4.2 pin skew**: generated code mixes `Aeneas.Std.core` and
  `CoreModels.core` trait dictionaries (`BuiltinClone`); `Stmt`'s derived
  Clone is opaque because of it. Newer hax (main pins hax-lean v0.3.39,
  aeneas build-41977a5) may fix this — evaluate upgrading in M1.
- **`fmt` back-reference triples**: axioms seeded for opaque `Debug::fmt`
  carry an extra borrow back-reference; curated to the pair shape.
- **CoreModels gaps** (hax-lean v0.3.30): no Ord/PartialOrd/Hash for
  Vec/String/Array/Option/Pair, no Clone/PartialEq for String, no BTreeMap —
  all modeled in `volar-ir-common`'s Assumptions extension block; upstream
  candidates.
- **volar-provenance scenario dropped**: aeneas emits a duplicate
  `corecloneCloneInst` field for the multi-Clone-bound `ProvenanceHandler`
  trait; the dictionary is hand-modeled in volar-ir-core's Assumptions.
- **Pre-publish deps**: llvm-bridge's public history lacks four crates used
  by volar-ir/cirrus members → `sources-patches/*.exclude-members` drops
  those members from the scratch checkouts. cirrus-ert-core's spurious
  llvm-bridge dependency was refactored away upstream (cirrus@23d2713:
  `SelectEmitter`/`select` vendored into cirrus-core).
- **macOS `/var` symlink**: all paths in scripts are physical (`pwd -P`);
  logical/physical mixes cause phantom cargo patch collisions.
- **Assumptions curation flow**: extract.sh reseeds the scratch package from
  committed `generated/` before each run so curated files persist;
  `scripts/resync-assumptions.sh` re-seeds from the template when the opaque
  set changes, preserving the extension block after the
  `-- EXTENSIONS` marker.
- **Single root lake package**: per-scenario `lake build` duplicates ~8 GiB
  of mathlib artifacts per package; the root `voof` package requires all
  scenario packages and builds them in one shared `.lake`.

## 8. Milestones

- **M0 — Scaffolding. DONE** (2026-11-01): voof live at
  `github.com/portal-co/voof`; `sources.toml`, scripts, pinned hax 0.4.2;
  three scenarios (`volar-side`, `volar-ir-common`, `volar-ir-core`)
  extracted and building green in CI with checked-in output; dedup gate
  (103 portal-co crates, one instance each); `sources-bump.yml` weekly PR
  workflow. Findings in §7a.
- **M1 — Stage-1 coverage (in progress).** `volar-spec-garble` extracts
  and builds (with the §3a patch set). Remaining: `volar-ir-passes`
  const-fold scenario, `cirrus-core` scenario, first `Verification/`
  proof (garble open∘share correctness). Worktree mode
  (`VOOF_SRC_MODE=worktree`) supports pinning any branch's rev for
  coordinated in-flight work without touching sibling mains.
- **M2 — IR remodeling.** Hand-written Lean semantics for the volar-ir core
  IR in `proofs/`, with a refinement/adequacy statement relating it to the
  extracted types.
- **M3 — First pass-correctness proof.** Constant folding (then DCE, CSE)
  proven semantics-preserving against the M2 semantics.
- **M4 — Crypto proof binding, first instance.** One volar-spec primitive
  (e.g. garbling scheme correctness) proven against a Lean spec, using
  `Assumptions/` models for the RustCrypto primitives; `hax-lib` annotations
  upstream if needed.
- **M5 — Steady state.** Stage-2 crates onboarded; pass-correctness and
  crypto bindings become the expected accompaniment to new passes/primitives.

## 9. Risks and open questions

- **hax Lean backend maturity** — it is younger than the F* backend; expect
  extraction bugs. Mitigation: pinned hax rev, narrow scenarios, willingness
  to carry a small fork patch set (hax is a git dep, so `--rev` on our fork
  is easy).
- **Lean toolchain skew across scenarios** — each generated package pins its
  own `lean-toolchain`; a hax upgrade may bump them all at once. CI must
  assert they are identical, or `require`-ing them from the root package
  breaks.
- **Unsupported Rust in wanted code** — interior mutability/`unsafe` in IR
  arenas or crypto code will force either upstream refactors (preferred; they
  also help the Rust code) or `Assumptions/` stubs that weaken the theorems.
  Track per-scenario "extracted vs. stubbed" ratios in a coverage doc.
- **Patch-block skew** — the generated config must cover every crate
  consumed from each patched URL; a workspace adding a new git dep on a
  sibling repo could slip past a stale list. Mitigation: the crate list is
  derived from the pinned checkouts at sync time, and `check-dedup.sh` fails
  CI on any duplicate resolution.
- **CI build times** — mathlib + Aeneas prelude are heavy; rely on `lake exe
  cache get` and aggressive Lake caching from day one.

## 10. Immediate next actions

1. Create `github.com/portal-co/voof` (public, matching the three source
   repos), push this repo.
2. Add `sources.toml` pinned to current `main` of all three repos;
   `scripts/sync.sh`.
3. `scripts/setup.sh` + `toolchain.toml`; verify `cargo hax --version` and
   `cargo hax tools install` locally.
4. Author `hax-configs/volar-ir__volar-ir__core.hax.toml` with a narrow
   include list; run first extraction locally; commit `generated/`.
5. Wire `extract-check.yml` and `lake-build.yml`; first green run closes M0.
