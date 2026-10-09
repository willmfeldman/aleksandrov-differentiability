module

public import AleksandrovDifferentiability.Analysis.Directional.FullMeasure
public import AleksandrovDifferentiability.Analysis.EstimateAssembly

/-!
# Directional full-measure assembly

This file assembles full-measure hypotheses for finite directional quadratic data into
almost-everywhere second-order differentiability conclusions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Conditional assembly from a full-measure finite slice-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure compatible finite slice-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure symmetric-compatible finite slice-estimate set when
pointwise reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure compatible finite quotient-slice set when pointwise
reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure symmetric-compatible finite quotient-slice set when
pointwise reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure finite slice quotient-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- If the directional line-scalar estimate sets for the directions `v i` and `v i + v j` have
full measure in `s`, and polarized reconstruction holds on the slice set, then `u` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceEstimateSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

/-- Quotient-estimate version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

end AleksandrovDifferentiability
