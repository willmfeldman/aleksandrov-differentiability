import AleksandrovDifferentiability.Analysis.EstimateAssembly
import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence
import AleksandrovDifferentiability.Statements.OneDimensional.Scalar

/-!
# One-dimensional theorem boundary

This file names the remaining one-dimensional scalar estimate target and connects it to the
real-line specialization of the convex Aleksandrov statement.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- A smooth sanity-check version of the one-dimensional scalar estimate target: if a real
function is `C^2` on an open convex domain, then the scalar quadratic estimate holds at every
point of the domain, hence the exceptional set is empty up to measure. -/
theorem measure_diff_realScalarQuadraticEstimateSet_eq_zero_of_contDiffOn_two
    {Ω : Set ℝ} {f : ℝ → ℝ} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hf : ContDiffOn ℝ 2 f Ω) :
    volume (Ω \ realScalarQuadraticEstimateSet f) = 0 := by
  have hsubset : Ω \ realScalarQuadraticEstimateSet f ⊆ (∅ : Set ℝ) := by
    intro x hx
    rcases hx with ⟨hxΩ, hxnot⟩
    exact hxnot
      (realScalarQuadraticEstimateAt_of_contDiffOn_two_of_mem_interior
        (s := Ω) (f := f) (x := x) hΩconv (by simpa [hΩ.interior_eq] using hxΩ) hf)
  exact measure_mono_null hsubset (by simp)

/-- Smooth one-dimensional scalar estimate statement: this is a check of the final assembly
pipeline under a stronger `C^2` hypothesis than convexity alone. -/
def SmoothOneDimensionalScalarEstimateStatement : Prop :=
  ∀ (Ω : Set ℝ) (f : ℝ → ℝ), IsOpen Ω → Convex ℝ Ω → ContDiffOn ℝ 2 f Ω →
    volume (Ω \ realScalarQuadraticEstimateSet f) = 0

/-- The smooth one-dimensional scalar estimate statement follows from Mathlib Taylor. -/
theorem smoothOneDimensionalScalarEstimateStatement :
    SmoothOneDimensionalScalarEstimateStatement := by
  intro Ω f hΩ hΩconv hf
  exact measure_diff_realScalarQuadraticEstimateSet_eq_zero_of_contDiffOn_two
    (Ω := Ω) (f := f) hΩ hΩconv hf

/-- Smooth real-line Aleksandrov check: if the convex function is `C^2` on the open domain, then
the project a.e. Aleksandrov statement follows from Mathlib Taylor and the final assembly layer. -/
theorem convexAleksandrovAEStatement_real_of_contDiffOn_two
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hC2 : IsOpen Ω → ConvexOn ℝ Ω f → ContDiffOn ℝ 2 f Ω) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  exact secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet
    (μ := volume) hΩ.measurableSet
    (measure_diff_realScalarQuadraticEstimateSet_eq_zero_of_contDiffOn_two
      (Ω := Ω) (f := f) hΩ hf.1 (hC2 hΩ hf))

/-- Null-bad-set version of `convexAleksandrovAEStatement_real_of_contDiffOn_two`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_contDiffOn_two
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hC2 : IsOpen Ω → ConvexOn ℝ Ω f → ContDiffOn ℝ 2 f Ω) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  exact measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimateSet
    (μ := volume) hΩ.measurableSet
    (measure_diff_realScalarQuadraticEstimateSet_eq_zero_of_contDiffOn_two
      (Ω := Ω) (f := f) hΩ hf.1 (hC2 hΩ hf))

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_real_of_contDiffOn_two`. -/
theorem convexAleksandrovNullBadSetStatement_real_of_contDiffOn_two
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hC2 : IsOpen Ω → ConvexOn ℝ Ω f → ContDiffOn ℝ 2 f Ω) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_contDiffOn_two Ω f hC2)

end AleksandrovDifferentiability
