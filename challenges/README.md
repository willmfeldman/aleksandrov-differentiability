# Comparator challenges

This directory contains isolated Comparator workspaces for the public
`AleksandrovDifferentiability` API. Every workspace has:

- `Statement.lean`: the trusted mathematical claim, importing Mathlib only;
- `Challenge.lean`: the trusted wrapper with a `sorry`, importing `Statement`;
- `Solution.lean`: the proof wrapper, importing both `Statement` and the project;
- `config.json`: theorem names and the exact permitted-axiom set; and
- `lakefile.toml`: a standalone Lake workspace whose default target is only `Challenge`.

Keeping the claim in `Statement.lean` gives both wrappers one statement surface. Comparator is
still authoritative: a shared source file reduces accidental drift but does not replace the
kernel, dependency, and permitted-axiom checks.

## What ordinary CI establishes

CI catches syntax, elaboration, and missing-proof regressions. Exact equality between trusted
challenge statements and solution statements is checked only by the release comparator workflow.

The internal `AleksandrovDifferentiability.Comparator` target is an API smoke-test suite. It checks
that public names and elementary consequences remain usable; it is not a theorem comparator.

## Release gate

The release workflow is `.github/workflows/release-comparator.yml`, dispatched manually
(`workflow_dispatch`) on a standard GitHub-hosted Linux runner (`ubuntu-latest`). It frees runner
disk, downloads the Mathlib cache and builds the trusted library, validates the challenge inventory
against `formalization.yaml` (`scripts/check-comparator-inventory.rb`), installs the pinned tools
(`scripts/release-comparator.sh install`), builds each trusted `Challenge` target outside the
sandbox, and then runs Comparator on every `challenges/*/config.json`
(`scripts/release-comparator.sh run`).

Pinned release tools:

- Lean and Mathlib: `v4.30.0`;
- Comparator: `d03acab154d269c06e60e4de7e4cc85deebff94b`;
- `lean4export`: `a3e35a584f59b390667db7269cd37fca8575e4bf`, built with this repository's
  `lean-toolchain`; and
- `landrun`: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` (pinned from `main`).

Every workspace sets `packagesDir = "../../.lake/packages"` in its `lakefile.toml` (and records
the same folder in its `lake-manifest.json`), so all workspaces share the root workspace's
dependency checkouts and builds. The manifests lock the same revisions as the root manifest.
Comparator's sandbox can read that shared folder but cannot write to it or reach the network,
which is why the library and the trusted `Challenge` targets are built before Comparator runs.

Comparator runs under `landrun` without the additional `systemd-run` containment that upstream
recommends for a full adversarial guarantee, so a passing run establishes Comparator's statement,
kernel, and permitted-axiom checks, not that stronger sandbox claim.

## Trusted release order

1. Start from a clean checkout of the exact release commit on a fresh hosted runner.
2. Build the trusted library and validate the challenge inventory.
3. Install the pinned Comparator, `lean4export`, and `landrun` revisions.
4. Build only the trusted `Challenge` targets, then run Comparator for every configuration.
5. Upload the attestation and complete logs as a workflow artifact.

Do not run `lake build Solution`, elaborate `Solution.lean`, or otherwise compile
solver-controlled sources in the release workspace before comparison. This ordering follows
[Comparator's documented threat model](https://github.com/leanprover/comparator).

## Classification

Release theorem comparators:

- `headline-mathlib-vocabulary`: the full theorem in Mathlib vocabulary;
- `statement-predicate`: the named statement layer; and
- `bounded-abs-headline`: a genuinely nonsmooth convex function, combining the a.e. theorem,
  failure at zero, and existence on a bounded positive-measure interval.

Additional downstream/API checks:

- `norm-convex-headline`: a generic norm application;
- `second-order-witness-interface`: the definitional witness shape; and
- `affine-model-case`: an elementary model case.

The root API-smoke target additionally checks constant functions, export/import surfaces, the
gradient bridge, and other named interfaces.

## Evidence and publication

The workflow artifact `comparator-attestation-<commit>` contains `attestation.json` (tested commit
and tree SHA, Lean and Mathlib revisions, all three external-tool commit hashes, every
configuration result, and the exact permitted-axiom policy) and complete per-configuration logs.

Before publishing a version tag, dispatch the workflow against the exact release commit on the
public repository and require it to pass. Then tag that same commit and attach the attestation
artifact to the GitHub release.

## Acceptance matrix

| Check | Pull requests | Release |
|---|---:|---:|
| Full Lake build | Required | Required (CI, and before Comparator) |
| Proof-integrity scan | Required | Required |
| API smoke tests | Required | Required |
| Challenge/solution elaboration | Required | Required |
| Exact axiom checks | Required | Required |
| Actual Comparator execution | Optional | Required |
| Comparator attestation artifact | — | Required |
| Versioned tag on the compared commit | — | Required |
