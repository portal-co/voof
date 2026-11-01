#!/usr/bin/env bash
# build-lean.sh — build everything through the root `voof` package, which
# requires each generated scenario package by path. One shared .lake means
# mathlib/Aeneas are fetched and built once (per-scenario .lake dirs would
# each duplicate ~8 GiB of mathlib artifacts).
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get
lake build
