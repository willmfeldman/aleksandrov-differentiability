module

public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Endpoint

/-!
# Countable interval reductions for Stieltjes coordinate-slice maximal sets

This file connects endpoint-average measurability to fixed-interval average maps and the
countable interval formulation of the source-local maximal bad sets.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

namespace CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval

/-- Endpoint-expression measurability gives fixed-interval average-map measurability for genuine
intervals. -/
theorem fixedIntervalAverageMeasurable_of_endpointAverage
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hend :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b) :
    CoordinateSliceConvexSourceRightDerivStieltjesFixedIntervalAverageMeasurable u hu a b := by
  intro i k
  convert hend i k using 1
  ext y
  exact coordinateSliceConvexSourceRightDerivStieltjes_average_eq_endpointAverageExpression
    i (hab k) y

/-- An admissible interval enumeration and the concrete reverse-cover direction give the
countable fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_reverseCover
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover.of_reverseCover
    hadm hreverse

/-- A rational interval enumeration and rational refinement give the concrete reverse-cover
direction for convex Stieltjes slices. -/
theorem reverseCover_of_rationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
      u hu a b t :=
  by
    open CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover in
    exact of_rationalRefinement henum hrefine

/-- Inner-rational refinement gives the concrete rational-refinement target for convex Stieltjes
slices. -/
theorem rationalRefinement_of_inner
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement u hu t := by
  exact CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.of_inner hrefine

/-- Sequential inner-rational approximation gives the concrete inner-rational refinement target
for convex Stieltjes slices. -/
theorem innerRationalRefinement_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
      u hu t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.inner_of_tendsto
    happrox

/-- Sequential inner-rational mass approximation gives the concrete inner-rational refinement
target for convex Stieltjes slices. -/
theorem innerRationalRefinement_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
      u hu t :=
  innerRationalRefinement_of_tendsto
    (CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.tendsto_of_massTendsto
      hmassApprox)

end CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval

end AleksandrovDifferentiability
