# voof

Lean 4 verification project for
[`portal-co/volar`](https://github.com/portal-co/volar),
[`portal-co/volar-ir`](https://github.com/portal-co/volar-ir), and
[`portal-co/cirrus`](https://github.com/portal-co/cirrus).

Rust source is extracted to Lean with [hax](https://hax.cryspen.com/)
(Charon + Aeneas, Lean backend). Generated Lean is **checked in** under
`generated/`; CI regenerates it from the pinned revs in `sources.toml` and
fails on any diff, then builds all Lean packages.

Long-term goals: remodel the IRs in Lean, prove compiler passes correct, and
bind the cryptosystems to Lean specs. See
[`docs/lean-verification-plan.md`](docs/lean-verification-plan.md).

## Layout

- `sources.toml` — pinned source repo revs.
- `toolchain.toml` — pinned hax version.
- `hax-configs/` — one `<Scenario>.hax.toml` per extraction target.
- `generated/<Scenario>/` — checked-in hax output; `Extraction/` is
  regenerated, `Assumptions/` is curated, `Verification/` is hand-written.
- `proofs/` — root package for cross-scenario theorems (later).
- `scripts/` — `setup.sh`, `sync.sh`, `extract.sh`, `check-dedup.sh`,
  `bump.sh`, `build-lean.sh`.

## Quick start

```sh
scripts/setup.sh      # elan + pinned cargo-hax (+ Charon/Aeneas)
scripts/sync.sh       # clone pinned revs into .sources/, write dedup config
scripts/extract.sh    # regenerate all scenarios into generated/
scripts/build-lean.sh # lake build everything
scripts/check-dedup.sh # assert one instance per portal-co crate
```

Local development against existing sibling checkouts: set `VOOF_SRC_VOLAR`,
`VOOF_SRC_VOLAR_IR`, `VOOF_SRC_CIRRUS` — they must match `sources.toml`.
