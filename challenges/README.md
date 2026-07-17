# Comparator Challenges

This directory contains release comparator workspaces for the public
AleksandrovDifferentiability API. Each subdirectory is a standalone Lake
workspace with:

- `Challenge.lean`: trusted statement surface, importing `Mathlib` only.
- `Solution.lean`: solution proof, importing `AleksandrovDifferentiability`.
- `config.json`: comparator module names, theorem names, and permitted axioms.
- `lakefile.toml`: local workspace metadata pinned through the parent project.

The `Challenge.lean` files restate any project-local vocabulary inline, rather
than importing the library. The `Solution.lean` files discharge the same theorem
names through the public root import.

## Toolchain

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `v4.30.0`
- Comparator: `leanprover/comparator`, run in the maintainer's release
  environment (a sandboxed Linux setup with a `lean4export` build matching
  Lean `v4.30.0`).

Comparator is intentionally a release/manual gate rather than a per-commit CI
gate, because its Linux sandbox and exporter setup are heavier than the normal
Lake build. The `Challenge.lean` and `Solution.lean` files themselves are
elaborated by the repository CI on every push, so statement drift is caught
per commit even though the comparator run is manual.

## Acceptance

For each challenge directory:

1. Build the workspace with `lake build`.
2. Run comparator using the local `config.json`.
3. Confirm each theorem depends only on:
   `propext`, `Classical.choice`, and `Quot.sound`.

The current release set covers the headline theorem (stated in Mathlib
vocabulary), the statement predicate, two concrete headline applications, the
public second-order witness interface, and the affine model case.
