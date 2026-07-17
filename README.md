# Aleksandrov Differentiability

This repository formalizes the finite-dimensional convex Aleksandrov second-order
differentiability theorem in Lean.

The main exported theorem is:

```lean
import AleksandrovDifferentiability

#check AleksandrovDifferentiability.convexAleksandrovAE
```

The statement, quoted verbatim from
`AleksandrovDifferentiability/Statements/Aleksandrov/Final.lean` (inside
`namespace AleksandrovDifferentiability`, with `open MeasureTheory`), is:

```lean
theorem convexAleksandrovAE
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure E).restrict Ω), SecondOrderDifferentiableAt u x
```

In ordinary mathematical language: if `u : E -> R` is convex on an open convex subset `Ω` of a
finite-dimensional real inner product space, then `u` is second-order differentiable at
`volume.restrict Ω`-almost every point.

## Status

The theorem `AleksandrovDifferentiability.convexAleksandrovAE` builds successfully in the current
repository. The project is still research-oriented rather than a polished Mathlib contribution:
many supporting declarations are named to expose the proof route, and some long files remain
candidates for later structural cleanup.

## Proof Route

The formalization proceeds through a normalized cube theorem and then transports the result to
arbitrary finite-dimensional real inner product spaces. The main ingredients include:

- foundational predicates for second-order expansions, convex subgradients, and upper contacts;
- one-dimensional convex analysis and line-restriction lemmas;
- maximal and Stieltjes-measure estimates on cube slices;
- reconstruction of a quadratic second-order candidate from directional data;
- Rockafellar/Straszewicz-style exposed-point and subgradient-cluster arguments;
- localization and transport from source cubes to the final finite-dimensional statement.

The public theorem endpoint is in
`AleksandrovDifferentiability/Statements/Aleksandrov/Final.lean`, and it is re-exported by
`AleksandrovDifferentiability.lean`.

Secondary formalized infrastructure includes one-dimensional convex second-derivative statements
under `AleksandrovDifferentiability/Statements/OneDimensional/` and
Rockafellar/Straszewicz-style exposed-point and subgradient-cluster material under
`AleksandrovDifferentiability/Analysis/RockafellarCluster/`.

## Build

This project uses Lean `v4.30.0` and Mathlib `v4.30.0`, as recorded in `lean-toolchain`,
`lakefile.lean`, and `lake-manifest.json`.

```bash
lake build
```

For a smaller check while developing one file, run:

```bash
lake env lean path/to/file.lean
```

The GitHub Actions workflow `.github/workflows/ci.yml` runs the same build on pushes and pull
requests using `leanprover/lean-action@v1`, including the Mathlib cache.

## Formalization Metadata

The file `formalization.yaml` records the public theorem targets, the pinned Lean/Mathlib versions,
the root import, the expected build commands, and the comparator challenge set. It is intended for
readers and tooling that want a compact index of the formalization without reverse-engineering the
Lake project.

The directory `challenges/` contains standalone comparator challenge workspaces. Their
`Challenge.lean` files import Mathlib only and restate project-local vocabulary inline; their
`Solution.lean` files import `AleksandrovDifferentiability` and discharge the corresponding
statements through the public API.

The file `AleksandrovDifferentiability/Comparator.lean` remains a Lean API-regression smoke-test
surface for public imports and supporting interfaces. It is wired as the default Lake target
`AleksandrovDifferentiabilityComparator`, but it is not a substitute for the external comparator
challenge workspaces.

## Layout

- `AleksandrovDifferentiability/Foundation/`
  contains the basic theorem-facing predicates.
- `AleksandrovDifferentiability/Geometry/`
  contains cube geometry and source-cube infrastructure.
- `AleksandrovDifferentiability/Analysis/`
  contains analytic supporting material, including one-dimensional convex facts, line restrictions,
  subgradient and exposed-point arguments, and quadratic reconstruction tools.
- `AleksandrovDifferentiability/Statements/`
  contains the theorem-boundary statements and the final exported Aleksandrov theorem.
- `challenges/`
  contains standalone comparator challenge workspaces for release verification.

## Credits

The mathematical result formalized here is A. D. Aleksandrov's 1939 almost-everywhere
second-order differentiability theorem for convex functions. The proof architecture also uses
classical convex analysis around exposed points and subgradient cluster sets, especially
Straszewicz's theorem and results from R. Tyrrell Rockafellar's *Convex Analysis*.

The original reference is A. D. Aleksandrov, "Almost everywhere existence of the second
differential of a convex function and some properties of convex surfaces connected with it"
(Russian), Leningrad State University Annals [Uchenye Zapiski], Mathematics Series 6 (1939),
3-35.

The early source work for this project was based on Jonas Hirsch's paper, *A note on the a.e.
second-order differentiability of rank-one convex functions*, arXiv:2511.08397. Local preparatory
notes specialized that source from rank-one convex functions on matrix spaces to convex functions
on finite-dimensional real vector spaces; those notes were significantly modified with assistance
from AI coding agents under human supervision and are not part of the public release.

The formalization depends on Lean and Mathlib. The Lean code was developed primarily with
AI coding agents under human supervision. Public attribution and citation metadata are kept at
the repository level in `CITATION.cff` and `formalization.yaml`; Lean source headers intentionally
omit per-file author lines.

## License

This repository is released under the Apache License 2.0. See `LICENSE`.

## Citation

If you cite this repository, please use the metadata in `CITATION.cff`.
