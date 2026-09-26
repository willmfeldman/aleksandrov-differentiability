module

public import AleksandrovDifferentiability.Analysis.AverageRemainder
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar

/-!
# One-dimensional scalar estimate theorem

The scalar one-dimensional target and the convex-function proof route through the
right-derivative average remainder.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- One-dimensional scalar-estimate target for convex functions: on every open convex subset of
`ℝ`, the named scalar quadratic estimate set has full measure. -/
def ConvexOneDimensionalScalarEstimateStatement : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    volume (Ω \ realScalarQuadraticEstimateSet f) = 0

/-- Punctured normalized quotient version of
`ConvexOneDimensionalScalarEstimateStatement`. -/
def ConvexOneDimensionalScalarQuotientEstimateStatement : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    volume (Ω \ realScalarQuadraticQuotientEstimateSet f) = 0

/-- Pointwise one-dimensional analytic bridge still to be proved: at every point of an open
convex domain where both one-sided derivative functions are differentiable within the domain,
the scalar quadratic estimate holds. -/
def ConvexOneDimensionalDerivativeEstimateImplication : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    Ω ∩ oneSidedDerivDifferentiabilitySet Ω f ⊆ realScalarQuadraticEstimateSet f

/-- Punctured normalized quotient version of
`ConvexOneDimensionalDerivativeEstimateImplication`. -/
def ConvexOneDimensionalDerivativeQuotientEstimateImplication : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    Ω ∩ oneSidedDerivDifferentiabilitySet Ω f ⊆ realScalarQuadraticQuotientEstimateSet f

/-- Sharper pointwise one-dimensional analytic bridge still to be proved: at every derivative-good
point of an open convex domain, the affine remainder is asymptotically the average of the endpoint
right-derivative increment. -/
def ConvexOneDimensionalAverageRemainderImplication : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    Ω ∩ oneSidedDerivDifferentiabilitySet Ω f ⊆ rightDerivAverageRemainderSet f

/-- Still sharper pointwise one-dimensional bridge: at derivative-good points of an open convex
domain, the affine remainder has the local interval-integral representation in terms of the
project-local right derivative. -/
def ConvexOneDimensionalIntegralRemainderImplication : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → ConvexOn ℝ Ω f →
    Ω ∩ oneSidedDerivDifferentiabilitySet Ω f ⊆ {x | HasRightDerivIntegralRemainderAt f x}

/-- The local scalar estimate target implies its punctured normalized quotient version. -/
theorem convexOneDimensionalScalarQuotientEstimateStatement_of_scalarEstimateStatement
    (h : ConvexOneDimensionalScalarEstimateStatement) :
    ConvexOneDimensionalScalarQuotientEstimateStatement := by
  intro Ω f hΩ hf
  refine measure_mono_null ?_ (h Ω f hΩ hf)
  intro x hx
  rcases hx with ⟨hxΩ, hxQuotient⟩
  refine ⟨hxΩ, ?_⟩
  intro hxEstimate
  exact hxQuotient
    (realScalarQuadraticEstimateSet_subset_realScalarQuadraticQuotientEstimateSet hxEstimate)

/-- The local pointwise derivative-good-set bridge implies its punctured normalized quotient
version. -/
theorem convexOneDimensionalDerivativeQuotientEstimateImplication_of_derivativeEstimateImplication
    (h : ConvexOneDimensionalDerivativeEstimateImplication) :
    ConvexOneDimensionalDerivativeQuotientEstimateImplication := by
  intro Ω f hΩ hf x hx
  exact realScalarQuadraticEstimateSet_subset_realScalarQuadraticQuotientEstimateSet
    (h Ω f hΩ hf hx)

/-- The averaged-remainder pointwise bridge implies the scalar-estimate pointwise bridge. -/
theorem convexOneDimensionalDerivativeEstimateImplication_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) :
    ConvexOneDimensionalDerivativeEstimateImplication := by
  intro Ω f hΩ hf x hx
  have hxInterior : x ∈ interior Ω := by
    simpa [hΩ.interior_eq] using hx.1
  exact realScalarQuadraticEstimateAt_of_mem_oneSidedDerivDifferentiabilitySet_of_averageRemainder
    (S := Ω) (f := f) (x := x) hxInterior hx.2 (h Ω f hΩ hf hx)

/-- The local interval-integral representation bridge implies the averaged-remainder bridge. -/
theorem convexOneDimensionalAverageRemainderImplication_of_integralRemainderImplication
    (h : ConvexOneDimensionalIntegralRemainderImplication) :
    ConvexOneDimensionalAverageRemainderImplication := by
  intro Ω f hΩ hf x hx
  have hxInterior : x ∈ interior Ω := by
    simpa [hΩ.interior_eq] using hx.1
  exact ConvexOn.hasRightDerivAverageRemainderAt_of_good_of_integralRemainder
    (S := Ω) (f := f) (x := x) hf hxInterior hx.2 (h Ω f hΩ hf hx)

/-- The local affine-remainder integral representation bridge holds for convex functions. -/
theorem convexOneDimensionalIntegralRemainderImplication :
    ConvexOneDimensionalIntegralRemainderImplication := by
  intro Ω f hΩ hf x hx
  have hxInterior : x ∈ interior Ω := by
    simpa [hΩ.interior_eq] using hx.1
  exact ConvexOn.hasRightDerivIntegralRemainderAt
    (S := Ω) (f := f) (x := x) hf hxInterior

/-- The averaged-remainder pointwise bridge holds for convex functions. -/
theorem convexOneDimensionalAverageRemainderImplication :
    ConvexOneDimensionalAverageRemainderImplication :=
  convexOneDimensionalAverageRemainderImplication_of_integralRemainderImplication
    convexOneDimensionalIntegralRemainderImplication

/-- The pointwise bridge from one-sided derivative differentiability to scalar quadratic
estimates implies the one-dimensional full-measure scalar-estimate target. -/
theorem convexOneDimensionalScalarEstimateStatement_of_derivativeEstimateImplication
    (h : ConvexOneDimensionalDerivativeEstimateImplication) :
    ConvexOneDimensionalScalarEstimateStatement := by
  intro Ω f hΩ hf
  have hnullInterior :
      volume (interior Ω \ oneSidedDerivDifferentiabilitySet Ω f) = 0 :=
    ConvexOn.measure_interior_diff_oneSidedDerivDifferentiabilitySet_eq_zero
      (S := Ω) (f := f) hf
  have hnull : volume (Ω \ oneSidedDerivDifferentiabilitySet Ω f) = 0 := by
    simpa [hΩ.interior_eq] using hnullInterior
  refine measure_mono_null ?_ hnull
  intro x hx
  rcases hx with ⟨hxΩ, hxEstimate⟩
  refine ⟨hxΩ, ?_⟩
  intro hxGood
  exact hxEstimate (h Ω f hΩ hf ⟨hxΩ, hxGood⟩)

/-- The quotient pointwise bridge from one-sided derivative differentiability to scalar
quadratic estimates implies the one-dimensional full-measure quotient-estimate target. -/
theorem convexOneDimensionalScalarQuotientEstimateStatement_of_derivativeQuotientEstimateImplication
    (h : ConvexOneDimensionalDerivativeQuotientEstimateImplication) :
    ConvexOneDimensionalScalarQuotientEstimateStatement := by
  intro Ω f hΩ hf
  have hnullInterior :
      volume (interior Ω \ oneSidedDerivDifferentiabilitySet Ω f) = 0 :=
    ConvexOn.measure_interior_diff_oneSidedDerivDifferentiabilitySet_eq_zero
      (S := Ω) (f := f) hf
  have hnull : volume (Ω \ oneSidedDerivDifferentiabilitySet Ω f) = 0 := by
    simpa [hΩ.interior_eq] using hnullInterior
  refine measure_mono_null ?_ hnull
  intro x hx
  rcases hx with ⟨hxΩ, hxEstimate⟩
  refine ⟨hxΩ, ?_⟩
  intro hxGood
  exact hxEstimate (h Ω f hΩ hf ⟨hxΩ, hxGood⟩)

/-- The averaged-remainder pointwise bridge implies the one-dimensional scalar-estimate target. -/
theorem convexOneDimensionalScalarEstimateStatement_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) :
    ConvexOneDimensionalScalarEstimateStatement :=
  convexOneDimensionalScalarEstimateStatement_of_derivativeEstimateImplication
    (convexOneDimensionalDerivativeEstimateImplication_of_averageRemainderImplication h)

/-- The averaged-remainder pointwise bridge implies the one-dimensional quotient-estimate target. -/
theorem convexOneDimensionalScalarQuotientEstimateStatement_of_averageRemainderImplication
    (h : ConvexOneDimensionalAverageRemainderImplication) :
    ConvexOneDimensionalScalarQuotientEstimateStatement :=
  convexOneDimensionalScalarQuotientEstimateStatement_of_derivativeQuotientEstimateImplication
    (convexOneDimensionalDerivativeQuotientEstimateImplication_of_derivativeEstimateImplication
      (convexOneDimensionalDerivativeEstimateImplication_of_averageRemainderImplication h))

/-- The pointwise derivative-good-set bridge holds for convex one-dimensional functions. -/
theorem convexOneDimensionalDerivativeEstimateImplication :
    ConvexOneDimensionalDerivativeEstimateImplication :=
  convexOneDimensionalDerivativeEstimateImplication_of_averageRemainderImplication
    convexOneDimensionalAverageRemainderImplication

/-- The punctured quotient derivative-good-set bridge holds for convex one-dimensional functions. -/
theorem convexOneDimensionalDerivativeQuotientEstimateImplication :
    ConvexOneDimensionalDerivativeQuotientEstimateImplication :=
  convexOneDimensionalDerivativeQuotientEstimateImplication_of_derivativeEstimateImplication
    convexOneDimensionalDerivativeEstimateImplication

/-- The one-dimensional scalar-estimate target holds for convex functions. -/
theorem convexOneDimensionalScalarEstimateStatement :
    ConvexOneDimensionalScalarEstimateStatement :=
  convexOneDimensionalScalarEstimateStatement_of_averageRemainderImplication
    convexOneDimensionalAverageRemainderImplication

/-- The one-dimensional punctured quotient scalar-estimate target holds for convex functions. -/
theorem convexOneDimensionalScalarQuotientEstimateStatement :
    ConvexOneDimensionalScalarQuotientEstimateStatement :=
  convexOneDimensionalScalarQuotientEstimateStatement_of_averageRemainderImplication
    convexOneDimensionalAverageRemainderImplication

end AleksandrovDifferentiability
