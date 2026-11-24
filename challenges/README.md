# Comparator challenges

This directory contains an isolated Comparator workspace for the public
`AleksandrovDifferentiability` API, `headline-mathlib-vocabulary`. Every file in it is a Lean
module. The workspace has:

- `Vocabulary.lean`: the trusted mathematical claim, importing Mathlib only;
- `Challenge.lean`: the trusted, self-contained challenge with a `sorry`. Its vocabulary block,
  between `-- BEGIN GENERATED VOCABULARY` and `-- END GENERATED VOCABULARY`, is generated from
  `Vocabulary.lean` by `python3 scripts/challenge-prep.py sync`, so it imports Mathlib only;
- `Solution.lean`: the proof wrapper, importing both `Vocabulary` and the project;
- `config.json`: theorem names and the exact permitted-axiom set; and
- `lakefile.toml`: a standalone Lake workspace whose default target is only `Challenge`.

Edit only `Vocabulary.lean`, then run `sync`. `python3 scripts/challenge-prep.py check` (run in CI)
fails if the generated block and `Vocabulary.lean` disagree. Comparator is still authoritative: it
compares every declaration reached from the compared statement by name and by value, and checks
the kernel, dependencies, and permitted axioms.

## What ordinary CI establishes

CI catches syntax, elaboration, and missing-proof regressions. Exact equality between trusted
challenge statements and solution statements is checked only by the release comparator workflow.

The internal `AleksandrovDifferentiability.Comparator` target is an API smoke-test suite. It checks
that public names and elementary consequences remain usable; it is not a theorem comparator.

## Release gate

The release workflow is `.github/workflows/release-comparator.yml`. It runs on a standard
GitHub-hosted Linux runner (`ubuntu-latest`) when dispatched manually (`workflow_dispatch`) and,
in the public repository, on pushes of `release/**` branches. Version tags do not trigger it: a
tag goes on a commit whose dispatched run already passed. It frees runner disk, downloads the Mathlib cache
and builds the trusted library, validates the challenge inventory against `formalization.yaml`
(`scripts/check-formalization-manifest.rb --metadata-only`), installs bubblewrap and allows
unprivileged user namespaces (`scripts/release-comparator.sh install`), builds each trusted
`Vocabulary` and `Challenge` target outside the sandbox, and then judges every
`challenges/*/config.json` with the pinned toolchain's `lake comparator`
(`scripts/release-comparator.sh run`).

Release tools: Lean and Mathlib `v4.36.0`. There are no separately pinned tools: `lake comparator`,
the exporter (`leanexport`) and every external checker ship with the toolchain in `lean-toolchain`,
so the toolchain pin is the tool pin. The workflow runs `lake comparator --paranoid`, so besides
Lean's own kernel the solution must also be accepted by every checker bundled with the toolchain
(`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche` and `con-ron`).

`lake comparator` evaluates the configuration and builds and exports the code inside a `bwrap`
sandbox: `/` is read-only, home directories are hidden, only `.lake` is writable, and the build,
the export and the checkers run without network. Because the sandbox hides home directories and
the workspace reaches the root project by relative path, a checkout under a home directory (as on
hosted runners) is judged from a copy under `/srv/comparator-work`.

Every workspace sets `packagesDir = "../../.lake/packages"` in its `lakefile.toml` (and records
the same folder in its `lake-manifest.json`), so all workspaces share the root workspace's
dependency checkouts and builds. The manifests lock the same revisions as the root manifest.
The library and the trusted `Challenge` targets are built before Comparator runs, so the sandbox
finds the dependency builds already in place.

## Trusted release order

1. Start from a clean checkout of the exact release commit on a fresh hosted runner.
2. Build the trusted library and validate the challenge inventory.
3. Install bubblewrap and allow unprivileged user namespaces.
4. Build only the trusted `Vocabulary` and `Challenge` targets, then run `lake comparator
   --paranoid` for every configuration, from a copy outside the home directories.
5. Upload the attestation and complete logs as a workflow artifact.

Do not run `lake build Solution`, elaborate `Solution.lean`, or otherwise compile
solver-controlled sources outside the sandbox before comparison.

## Classification

Release theorem comparator:

- `headline-mathlib-vocabulary`: the full theorem, stated in Mathlib vocabulary only.

Because the headline uses only Mathlib definitions, no separate model-case or interface
workspaces are needed. The root API-smoke target (`AleksandrovDifferentiability.Comparator`) checks
the named statement layer, the second-order witness interface, constant and affine model cases,
the norm and absolute-value examples, export/import surfaces, the gradient bridge, and other named
interfaces.

## Evidence and publication

The workflow artifact `comparator-attestation-<commit>` contains `attestation.json` (tested commit
and tree SHA, Lean and Mathlib revisions, the Lake and bubblewrap versions, whether the bundled checkers
ran, every configuration result, and the exact permitted-axiom policy) and complete per-configuration logs.

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
