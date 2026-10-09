module

public import AleksandrovDifferentiability.Statements.Cube.Envelope
public import AleksandrovDifferentiability.Analysis.EpigraphLineLift
public import AleksandrovDifferentiability.Analysis.LineIntegral

/-!
# Cube-local second-order assembly

This file records the final measure-theoretic assembly step in the source cube proof.  The
remaining mathematical work is pointwise: turn the source-route gradient expansion at a good point
into `SecondOrderDifferentiableAt`.  Once that pointwise bridge is available, the a.e. cube
statement follows immediately from the countable good-set/envelope theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open Asymptotics
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

/-- At a source good point, every subgradient on the ambient source cube is the Fréchet
gradient.

This is the base-point input in the source subgradient-extension argument.  The point `x` belongs
to `Q_1`, hence has a neighborhood inside `Q_3`, and membership in the good set includes
Fréchet differentiability at `x`. -/
theorem cubeGoodSet_subgradient_eq_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A : ℝ} {x p : SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u A)
    (hp : SubgradientOn (sourceOpenCube n 3) u x p) :
    p = frechetGradient u x := by
  rcases mem_cubeGoodSet.mp hxgood with ⟨hxQ, hdiff, _hopening⟩
  have hxInterior : x ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hxQ
  have hs : sourceOpenCube n 3 ∈ 𝓝 x :=
    (isOpen_sourceOpenCube (n := n) 3).mem_nhds (interior_subset hxInterior)
  change p = gradient u x
  exact hp.eq_gradient_of_differentiableAt hs hdiff

/-- Cube-local subgradient extension from cluster-gradient density.

This is the source `subgradient-extension` lemma with the hard convex-analysis input exposed as
`hdensity`.  The estimate `hgradient` is the moving-base gradient estimate produced from the
good-point gradient expansion in the LaTeX proof. -/
theorem sourceCube_subgradientLinearization_of_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hgradient : ∀ ε > 0,
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ᶠ w in 𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] y,
        ‖frechetGradient u w - (frechetGradient u x + B (y - x))‖ ≤
          ε * ‖y - x‖)
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y)))
    (hbase : ∀ p : SourceCubeSpace n,
      SubgradientOn (sourceOpenCube n 3) u x p → p = frechetGradient u x) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  HasSubgradientLinearizationOnAt.of_punctured_eventually_gradient_estimates_of_cluster_convexHull
    (domain := sourceOpenCube n 3)
    (D := sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
    (approach := sourceOpenCube n (3 / 2 : ℝ))
    (u := u) (G := frechetGradient u) (x := x) (p₀ := frechetGradient u x)
    (B := B) hgradient hdensity hbase

/-- Good-point version of the cube-local subgradient extension.

The abstract cluster-gradient bridge requires a separate base-point uniqueness hypothesis.  At a
good point this is automatic, because the good set records differentiability at the base point. -/
theorem sourceCube_good_subgradientLinearization_of_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient : ∀ ε > 0,
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ᶠ w in 𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] y,
        ‖frechetGradient u w - (frechetGradient u x + B (y - x))‖ ≤
          ε * ‖y - x‖)
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y))) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_subgradientLinearization_of_clusterConvexHull
    hgradient hdensity (fun _ hp => cubeGoodSet_subgradient_eq_frechetGradient hxgood hp)

/-- Good-point subgradient extension from the source-route gradient little-o expansion.

This is the cube-local form needed after the Lipschitz-envelope step: the envelope argument
produces a little-o expansion of `frechetGradient u` along the dense differentiability set
`D_{3/2}`.  The generic moving-base lemma converts that into the punctured estimates required by
the cluster-gradient subgradient bridge.  The remaining hypothesis is exactly the source
finite-dimensional density theorem for subgradients. -/
theorem sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hgradient :
      ((fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
          fun y => ‖y - x‖))
    (hdensity : ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
      ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
              (frechetGradient u) y))) :
    HasSubgradientLinearizationOnAt
      (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
      u x (frechetGradient u x) B :=
  sourceCube_good_subgradientLinearization_of_clusterConvexHull
    hxgood
    (HasSubgradientLinearizationOnAt.eventually_gradient_estimates_of_isLittleO hgradient)
    hdensity

/-- For a good point `x ∈ Q_1`, all sufficiently short source increments have their whole
unit parameter interval inside the interior of the line domain for `Q_3`. -/
theorem cubeGoodSet_eventually_uIcc_subset_interior_lineDomain
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ)) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      Set.uIcc (0 : ℝ) 1 ⊆ interior (lineDomain (sourceOpenCube n 3) x z) := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  filter_upwards [eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ] with
    z hzsegment t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using ht
  have ht_three_halves : x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ) :=
    hzsegment t htIcc
  have htInterior : x + t • z ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
      (by norm_num) ht_three_halves
  have htLine : t ∈ lineDomain (sourceOpenCube n 3) x z := by
    simpa [lineDomain] using interior_subset htInterior
  have hopen : IsOpen (lineDomain (sourceOpenCube n 3) x z) :=
    isOpen_lineDomain (s := sourceOpenCube n 3) (x := x) (v := z)
      (isOpen_sourceOpenCube (n := n) 3)
  exact mem_interior_iff_mem_nhds.mpr (hopen.mem_nhds htLine)

/-- Convex line-restriction right-derivative integrability on the unit segment, eventually in
the source increment. -/
theorem cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1 := by
  filter_upwards [cubeGoodSet_eventually_uIcc_subset_interior_lineDomain hxgood] with z hz
  exact ConvexOn.lineRestriction_intervalIntegrable_rightDeriv_of_uIcc_subset_interior
    (x := x) (v := z) hconvex hz

/-- Convex line-restriction right-derivative FTC representation on the unit segment, eventually
in the source increment. -/
theorem cubeGoodSet_eventually_lineRightDeriv_integral_repr
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t := by
  filter_upwards [cubeGoodSet_eventually_uIcc_subset_interior_lineDomain hxgood] with z hz
  exact ConvexOn.lineRestriction_sub_eq_integral_rightDeriv_of_uIcc_subset_interior
    (x := x) (v := z) hconvex hz

/-- For a good point `x ∈ Q_1`, all sufficiently short nontrivial segment parameters lie in the
ambient interior of `Q_3`. -/
theorem cubeGoodSet_eventually_segment_mem_interior_sourceOpenCube_three
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ)) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior (sourceOpenCube n 3) := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  filter_upwards [eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ] with z hzsegment
    t ht
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa using ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
  exact
    sourceOpenCube_subset_interior_of_le
      (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) (hzsegment t htIcc)

/-- Good-point second-order differentiability from subgradient linearization and the functional
line-subgradient lift interface.

This lower-level compatibility form keeps the functional line-subgradient lift as an explicit
hypothesis.  The preferred wrapper below supplies it from Mathlib Hahn-Banach separation. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientFunctional
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B)
    (hlift : ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain (sourceOpenCube n 3) x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional (sourceOpenCube n 3) u x z t q) :
    SecondOrderDifferentiableAt u x := by
  have hxQ : x ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hxgood).1
  exact
    HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineSubgradientFunctional hlin
      hconvex
      (eventually_sourceOpenCube_one_add_smul_mem_three_halves hxQ)
      (cubeGoodSet_eventually_segment_mem_interior_sourceOpenCube_three hxgood)
      (cubeGoodSet_eventually_lineRightDeriv_integral_repr hxgood hconvex)
      (cubeGoodSet_eventually_lineRightDeriv_intervalIntegrable hxgood hconvex)
      hlift

/-- Good-point second-order differentiability from subgradient linearization alone.

The line-subgradient ambient lift is supplied by the strict-epigraph separation theorem in
`ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen`, so no separate Hahn-Banach
hypothesis remains at this point. -/
theorem cubeGoodSet_secondOrderDifferentiableAt_of_subgradientLinearization
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {m : ℕ}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hxgood : x ∈ cubeGoodSet n u (m : ℝ))
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hlin :
      HasSubgradientLinearizationOnAt
        (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
        u x (frechetGradient u x) B) :
    SecondOrderDifferentiableAt u x :=
  cubeGoodSet_secondOrderDifferentiableAt_of_lineSubgradientFunctional
    hxgood hconvex hlin
    (Filter.Eventually.of_forall fun _z _t _ht _q hq =>
      ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen
        hconvex (isOpen_sourceOpenCube (n := n) 3) hq)

end AleksandrovDifferentiability
