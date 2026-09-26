module

public import AleksandrovDifferentiability.Analysis.EpigraphLineLift
public import AleksandrovDifferentiability.Analysis.LineRestriction
public import AleksandrovDifferentiability.Statements.Cube.Oscillation

/-!
# Cube-local endpoint attainment

This file packages the cube-local compactness/boundedness part of the endpoint-attainment step.
The remaining input is the support-function inequality expected from Mathlib's separation
theorem; the boundedness of the subdifferential on `Q_{3/2}` is supplied by the oscillation
estimate on `Q_3`.
-/

@[expose] public noncomputable section

open scoped Topology

namespace AleksandrovDifferentiability

/-- Cube-local right-endpoint attainment from the support-function inequality at a maximizing
subgradient.

The hypothesis `hmax_le` is the remaining separation-facing input.  Boundedness of the
subdifferential is obtained from boundedness of `u` on the normalized cube `Q_3`. -/
theorem ConvexOn.exists_sourceCube_subgradient_lineRightDeriv_eq_inner_of_boundedOn_of_isMaxOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x z : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hne : {p : SourceCubeSpace n |
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p}.Nonempty)
    (hmax_le : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
        IsMaxOn (fun q : SourceCubeSpace n => inner ℝ q z)
          {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ inner ℝ p z) :
    ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  have hinterior : x + t • z ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
      (by norm_num) hpoint
  have hbounded_subgradient :
      Bornology.IsBounded
        {p : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) p} :=
    sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves hbounded hpoint
  exact
    ConvexOn.exists_subgradient_lineRightDeriv_eq_inner_of_isBounded_of_forall_isMaxOn hu
      hinterior hne hbounded_subgradient hmax_le

/-- Cube-local right-endpoint attainment from the support-function inequality, with
subgradient nonemptiness supplied by epigraph separation on the open cube. -/
theorem ConvexOn.exists_sourceCube_subgradient_lineRightDeriv_eq_inner_of_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x z : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hmax_le : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
        IsMaxOn (fun q : SourceCubeSpace n => inner ℝ q z)
          {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ inner ℝ p z) :
    ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  have hpoint3 : x + t • z ∈ sourceOpenCube n 3 :=
    sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hpoint
  have hne :
      {p : SourceCubeSpace n |
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p}.Nonempty :=
    ConvexOn.subgradient_set_nonempty_of_isOpen hu (isOpen_sourceOpenCube (n := n) 3) hpoint3
  exact
    ConvexOn.exists_sourceCube_subgradient_lineRightDeriv_eq_inner_of_boundedOn_of_isMaxOn
      hu hbounded hpoint hne hmax_le

/-- Cube-local left-endpoint attainment from the support-function inequality at a minimizing
subgradient.

The hypothesis `hmin_le` is the remaining separation-facing input.  Boundedness of the
subdifferential is obtained from boundedness of `u` on the normalized cube `Q_3`. -/
theorem ConvexOn.exists_sourceCube_subgradient_lineLeftDeriv_eq_inner_of_boundedOn_of_isMinOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x z : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hne : {p : SourceCubeSpace n |
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p}.Nonempty)
    (hmin_le : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
        IsMinOn (fun q : SourceCubeSpace n => inner ℝ q z)
          {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
          inner ℝ p z ≤ leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :
    ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  have hinterior : x + t • z ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
      (by norm_num) hpoint
  have hbounded_subgradient :
      Bornology.IsBounded
        {p : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) p} :=
    sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves hbounded hpoint
  exact
    ConvexOn.exists_subgradient_lineLeftDeriv_eq_inner_of_isBounded_of_forall_isMinOn hu
      hinterior hne hbounded_subgradient hmin_le

/-- Cube-local left-endpoint attainment from the support-function inequality, with
subgradient nonemptiness supplied by epigraph separation on the open cube. -/
theorem ConvexOn.exists_sourceCube_subgradient_lineLeftDeriv_eq_inner_of_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x z : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hmin_le : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
        IsMinOn (fun q : SourceCubeSpace n => inner ℝ q z)
          {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
          inner ℝ p z ≤ leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :
    ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  have hpoint3 : x + t • z ∈ sourceOpenCube n 3 :=
    sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hpoint
  have hne :
      {p : SourceCubeSpace n |
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p}.Nonempty :=
    ConvexOn.subgradient_set_nonempty_of_isOpen hu (isOpen_sourceOpenCube (n := n) 3) hpoint3
  exact
    ConvexOn.exists_sourceCube_subgradient_lineLeftDeriv_eq_inner_of_boundedOn_of_isMinOn
      hu hbounded hpoint hne hmin_le

/-- Eventual line-subgradient functional lifts from cube-local endpoint support inequalities.

This is the direct interface for the later Mathlib-separation step: once separation proves the
maximal and minimal support inequalities along small segments, the existing endpoint bridge
produces functional lifts for all one-dimensional line subgradients. -/
theorem ConvexOn.eventually_sourceCube_lineSubgradient_liftsToAmbientFunctional_of_extrema
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hne : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        {p : SourceCubeSpace n |
          SubgradientOn (sourceOpenCube n 3) u (x + t • z) p}.Nonempty)
    (hmax_le : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ p : SourceCubeSpace n,
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
          IsMaxOn (fun q : SourceCubeSpace n => inner ℝ q z)
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
            rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ inner ℝ p z)
    (hmin_le : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ p : SourceCubeSpace n,
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
          IsMinOn (fun q : SourceCubeSpace n => inner ℝ q z)
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
            inner ℝ p z ≤ leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain (sourceOpenCube n 3) x z)
          (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional (sourceOpenCube n 3) u x z t q := by
  have hsegmentInterior : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior (sourceOpenCube n 3) := by
    filter_upwards [hpoint] with z hz t ht
    exact
      sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
        (by norm_num) (hz t ht)
  have hleft : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
          leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
    filter_upwards [hpoint, hne, hmin_le] with z hzpoint hznonempty hzmin t ht
    exact
      ConvexOn.exists_sourceCube_subgradient_lineLeftDeriv_eq_inner_of_boundedOn_of_isMinOn
        hu
        hbounded (hzpoint t ht) (hznonempty t ht) (hzmin t ht)
  have hright : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
    filter_upwards [hpoint, hne, hmax_le] with z hzpoint hznonempty hzmax t ht
    exact
      ConvexOn.exists_sourceCube_subgradient_lineRightDeriv_eq_inner_of_boundedOn_of_isMaxOn
        hu
        hbounded (hzpoint t ht) (hznonempty t ht) (hzmax t ht)
  exact
    ConvexOn.eventually_lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_attainment hu
      hsegmentInterior hleft hright

/-- Eventual line-subgradient functional lifts from cube-local endpoint support inequalities,
with subgradient nonemptiness supplied by epigraph separation on the open cube. -/
theorem ConvexOn.eventually_sourceCube_lineSubgradient_liftsToAmbientFunctional_auto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hpoint : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hmax_le : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ p : SourceCubeSpace n,
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
          IsMaxOn (fun q : SourceCubeSpace n => inner ℝ q z)
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
            rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ inner ℝ p z)
    (hmin_le : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ p : SourceCubeSpace n,
        SubgradientOn (sourceOpenCube n 3) u (x + t • z) p →
          IsMinOn (fun q : SourceCubeSpace n => inner ℝ q z)
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u (x + t • z) q} p →
            inner ℝ p z ≤ leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain (sourceOpenCube n 3) x z)
          (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional (sourceOpenCube n 3) u x z t q := by
  have hsegmentInterior : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior (sourceOpenCube n 3) := by
    filter_upwards [hpoint] with z hz t ht
    exact
      sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
        (by norm_num) (hz t ht)
  have hleft : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
          leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
    filter_upwards [hpoint, hmin_le] with z hzpoint hzmin t ht
    exact
      ConvexOn.exists_sourceCube_subgradient_lineLeftDeriv_eq_inner_of_boundedOn
        hu hbounded (hzpoint t ht) (hzmin t ht)
  have hright : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u (x + t • z) p ∧
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
    filter_upwards [hpoint, hmax_le] with z hzpoint hzmax t ht
    exact
      ConvexOn.exists_sourceCube_subgradient_lineRightDeriv_eq_inner_of_boundedOn
        hu hbounded (hzpoint t ht) (hzmax t ht)
  exact
    ConvexOn.eventually_lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_attainment hu
      hsegmentInterior hleft hright

end AleksandrovDifferentiability
