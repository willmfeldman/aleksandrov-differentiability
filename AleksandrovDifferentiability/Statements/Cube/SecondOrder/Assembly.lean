module

public import AleksandrovDifferentiability.Statements.Cube.SecondOrder.Pointwise

/-!
# Cube-local second-order a.e. assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientLinearization_bridge
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hsubgradientExtension :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B)
    (htaylor :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B →
            SecondOrderDifferentiableAt u x) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
by
  filter_upwards
    [ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_expansion_three_halves_of_convex
      hfiniteStatement hn hbounded hconvex] with x hx
  rcases hx with ⟨m, hxgood, B, hB⟩
  exact htaylor x m B hxgood hB (hsubgradientExtension x m B hxgood hB)

/-- Source-route a.e. second-order differentiability on `Q_1`, with the subgradient-extension
step reduced to the finite-dimensional cluster-density theorem.

The envelope theorem supplies the good point, the linear map `B`, and the gradient little-o
expansion.  The hypothesis `hdensity` is the remaining convex-analysis input identifying nearby
subgradients with the closed convex hull of cluster gradients.  The hypothesis `htaylor` is the
last integration step converting subgradient linearization into a second-order Taylor expansion. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y)))
    (htaylor :
      ∀ (x : SourceCubeSpace n) (m : ℕ) (B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ((fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖) →
            HasSubgradientLinearizationOnAt
              (sourceOpenCube n 3) (sourceOpenCube n (3 / 2 : ℝ))
              u x (frechetGradient u x) B →
            SecondOrderDifferentiableAt u x) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_subgradientLinearization_bridge
    hfiniteStatement hn hbounded hconvex
    (fun x m _ hxgood hB =>
      sourceCube_good_subgradientLinearization_of_gradientExpansion_and_clusterConvexHull
        hxgood hB (hdensity x m hxgood))
    htaylor

/-- Source-route a.e. second-order differentiability on `Q_1`, reduced to the finite-dimensional
cluster-density theorem for convex subgradients.

The line-subgradient lift is no longer an external hypothesis: it is supplied by Mathlib
Hahn-Banach separation through `ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdensity :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              p ∈ closure
                (convexHull ℝ
                  (HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y))) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity_and_taylor
    hfiniteStatement hn hbounded hconvex hdensity
    (fun _x _m _B hxgood _hgradient hlin =>
      cubeGoodSet_secondOrderDifferentiableAt_of_subgradientLinearization
        hxgood hconvex hlin)

end AleksandrovDifferentiability
