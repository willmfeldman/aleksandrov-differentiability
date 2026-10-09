module

public import AleksandrovDifferentiability.Analysis.Directional.Assembly
public import AleksandrovDifferentiability.Analysis.EstimateAssembly
public import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence

/-!
# Slice-reconstruction reductions to the a.e. theorem
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Theorem-boundary reduction from full measure of compatible finite directional slice data
plus pointwise reconstruction into polarized mixed-directional ambient estimates. -/
theorem convexAleksandrovAEStatement_of_compatibleSliceSet_polarized_reconstruction
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_compatibleSliceSet_polarized_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_compatibleSliceQuotientSet_polarized_reconstruction
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

end AleksandrovDifferentiability
