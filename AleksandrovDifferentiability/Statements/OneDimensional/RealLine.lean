module

public import AleksandrovDifferentiability.Analysis.EstimateAssembly
public import AleksandrovDifferentiability.Statements.Aleksandrov.Core
public import AleksandrovDifferentiability.Statements.OneDimensional.Scalar

/-!
# Real-line Aleksandrov theorem wrappers

Endpoint real-line forms of the one-dimensional scalar estimate theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Real-line conversion from domain-intersected null bad set to restricted-measure null bad set. -/
theorem convexAleksandrovNullBadSetStatement_real_of_onStatement
    {Ω : Set ℝ} {f : ℝ → ℝ}
    (h : ConvexAleksandrovNullBadSetOnStatement ℝ Ω f) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f := by
  intro hΩ hf
  have hAE : SecondOrderDifferentiableAEOn volume Ω f := by
    exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
      hΩ.measurableSet).mpr (h hΩ hf)
  exact restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn hAE

/-- Real-line theorem-boundary reduction from full measure of the named scalar estimate set. -/
theorem convexAleksandrovAEStatement_real_of_fullMeasure_scalarEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticEstimateSet f) = 0) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  exact secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hf)

/-- Real-line theorem-boundary reduction from full measure of the named scalar quotient-estimate
set. -/
theorem convexAleksandrovAEStatement_real_of_fullMeasure_scalarQuotientEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  exact secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hf)

/-- Null-bad-set theorem-boundary reduction from full measure of the named real-line scalar
estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticEstimateSet f) = 0) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  exact measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hf)

/-- Null-bad-set theorem-boundary reduction from full measure of the named real-line scalar
quotient-estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarQuotientEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  exact measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarQuotientEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hf)

/-- The scalar-estimate target implies the real-line Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_fullMeasure_scalarEstimateSet Ω f
    (fun hΩ hf => h Ω f hΩ hf)

/-- The scalar quotient-estimate target implies the real-line Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_real_of_oneDimensionalScalarQuotientEstimate
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_fullMeasure_scalarQuotientEstimateSet Ω f
    (fun hΩ hf => h Ω f hΩ hf)

/-- The pointwise derivative-good-set bridge implies the real-line Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_real_of_derivativeEstimateImplication
    (h : ConvexOneDimensionalDerivativeEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate
    (convexOneDimensionalScalarEstimateStatement_of_derivativeEstimateImplication h) Ω f

/-- The quotient pointwise derivative-good-set bridge implies the real-line Aleksandrov a.e.
statement. -/
theorem convexAleksandrovAEStatement_real_of_derivativeQuotientEstimateImplication
    (h : ConvexOneDimensionalDerivativeQuotientEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_oneDimensionalScalarQuotientEstimate
    (convexOneDimensionalScalarQuotientEstimateStatement_of_derivativeQuotientEstimateImplication
      h) Ω f

/-- The averaged-remainder pointwise bridge implies the real-line Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_real_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate
    (convexOneDimensionalScalarEstimateStatement_of_averageRemainderImplication h) Ω f

/-- Real-line Aleksandrov a.e. statement for convex functions. -/
theorem convexAleksandrovAEStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate
    convexOneDimensionalScalarEstimateStatement Ω f

/-- Null-bad-set form of
`convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarEstimate
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarEstimateSet Ω f
    (fun hΩ hf => h Ω f hΩ hf)

/-- Restricted-measure null-bad-set form of
`convexAleksandrovAEStatement_real_of_oneDimensionalScalarEstimate`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_oneDimensionalScalarEstimate
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarEstimate h Ω f)

/-- Null-bad-set form of
`convexAleksandrovAEStatement_real_of_oneDimensionalScalarQuotientEstimate`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarQuotientEstimate
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarQuotientEstimateSet Ω f
    (fun hΩ hf => h Ω f hΩ hf)

/-- Restricted-measure null-bad-set form of
`convexAleksandrovAEStatement_real_of_oneDimensionalScalarQuotientEstimate`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_oneDimensionalScalarQuotientEstimate
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarQuotientEstimate h Ω f)

/-- Null-bad-set form of
`convexAleksandrovAEStatement_real_of_derivativeEstimateImplication`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_derivativeEstimateImplication
    (h : ConvexOneDimensionalDerivativeEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarEstimate
    (convexOneDimensionalScalarEstimateStatement_of_derivativeEstimateImplication h) Ω f

/-- Restricted-measure null-bad-set form of
`convexAleksandrovAEStatement_real_of_derivativeEstimateImplication`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_derivativeEstimateImplication
    (h : ConvexOneDimensionalDerivativeEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real_of_derivativeEstimateImplication h Ω f)

/-- Null-bad-set form of
`convexAleksandrovAEStatement_real_of_derivativeQuotientEstimateImplication`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_derivativeQuotientEstimateImplication
    (h : ConvexOneDimensionalDerivativeQuotientEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarQuotientEstimate
    (convexOneDimensionalScalarQuotientEstimateStatement_of_derivativeQuotientEstimateImplication
      h) Ω f

/-- Restricted-measure null-bad-set form of
`convexAleksandrovAEStatement_real_of_derivativeQuotientEstimateImplication`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_derivativeQuotientEstimateImplication
    (h : ConvexOneDimensionalDerivativeQuotientEstimateImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real_of_derivativeQuotientEstimateImplication h Ω f)

/-- Null-bad-set form of
`convexAleksandrovAEStatement_real_of_averageRemainderImplication`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarEstimate
    (convexOneDimensionalScalarEstimateStatement_of_averageRemainderImplication h) Ω f

/-- Restricted-measure null-bad-set form of
`convexAleksandrovAEStatement_real_of_averageRemainderImplication`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real_of_averageRemainderImplication h Ω f)

/-- Real-line null-bad-set Aleksandrov statement for convex functions. -/
theorem convexAleksandrovNullBadSetOnStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_real_of_oneDimensionalScalarEstimate
    convexOneDimensionalScalarEstimateStatement Ω f

/-- Real-line restricted-measure null-bad-set Aleksandrov statement for convex functions. -/
theorem convexAleksandrovNullBadSetStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  convexAleksandrovNullBadSetStatement_real_of_onStatement
    (convexAleksandrovNullBadSetOnStatement_real Ω f)

end AleksandrovDifferentiability
