module

public import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence
public import AleksandrovDifferentiability.Analysis.Directional.Assembly
public import AleksandrovDifferentiability.Analysis.EstimateAssembly
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Frame
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Operators
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar
public import AleksandrovDifferentiability.Foundation.SecondOrder
public import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
public import AleksandrovDifferentiability.Statements.Aleksandrov.Core
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Core

/-!
# Slice-reconstruction reductions to null bad sets
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Null-bad-set theorem-boundary reduction from full measure of compatible finite directional
slice data plus pointwise reconstruction into polarized mixed-directional ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

end AleksandrovDifferentiability
