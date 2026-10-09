module

public import AleksandrovDifferentiability.Analysis.GoodSet
public import AleksandrovDifferentiability.Analysis.QuadraticTrap

/-!
# Assembly from quadratic estimates

This file packages the passage from full-measure sets carrying pointwise quadratic remainder
estimates to the project almost-everywhere differentiability conclusions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- If the named real-line scalar estimate set has full measure in `s`, then `f` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticEstimateSet f) = 0) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact realScalarQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- If the named real-line scalar quotient-estimate set has full measure in `s`, then `f` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact realScalarQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticEstimateSet f) = 0) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet hs hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarQuotientEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet hs hnull)

end AleksandrovDifferentiability
