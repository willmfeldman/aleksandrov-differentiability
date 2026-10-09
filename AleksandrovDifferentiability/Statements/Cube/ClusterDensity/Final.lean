module

public import AleksandrovDifferentiability.Statements.Cube.ClusterDensity.Ray
public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Wrappers

/-!
# Source-cube cluster-density final assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

set_option linter.unusedSectionVars false in
/-- Normalized source-cube Aleksandrov theorem from the standard compact-convex Straszewicz
theorem.

This is now the cleanest source-cube boundary: after the upper-contact/Stieltjes analysis and
Rockafellar directional outer-semicontinuity work, the only remaining external convex-geometry
input is `StraszewiczCompactConvexStatement` for the finite-dimensional source cube space. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_straszewiczCompactConvex
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz : StraszewiczCompactConvexStatement (SourceCubeSpace n)) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_convexSourceRightDerivStieltjes
    hn hbounded hconvex
    (SourceCubeSubgradientClusterDensity.of_straszewiczCompactConvex
      hn hbounded hconvex hstrasz)

set_option linter.unusedSectionVars false in
/-- Normalized source-cube Aleksandrov theorem for bounded convex functions.

This version discharges the compact-convex Straszewicz input using
`straszewiczCompactConvexStatement`. -/
theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_straszewiczCompactConvex
    hn hbounded hconvex
    (straszewiczCompactConvexStatement (E := SourceCubeSpace n))

end AleksandrovDifferentiability
