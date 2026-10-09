module

public import AleksandrovDifferentiability.Statements.Cube.Maximal
public import AleksandrovDifferentiability.Statements.Cube.FirstOrder

/-!
# Stieltjes coordinate-slice measures on source cubes

This file specializes the abstract coordinate-slice measure family from `Cube.Maximal` to the
Stieltjes measures of the project-local right derivatives of coordinate-line restrictions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-! ## Source-local clamped Stieltjes slices -/

/-- Coordinate-slice measure family obtained from the source-local clamped Stieltjes measure.

This construction only asks for monotonicity of the right derivative on the source interval
`[-2,2]`, and only for line bases in `Q_1`.  Outside those bases the family is filled with the
zero measure, which is harmless for the source bad sets. -/
def coordinateSliceSourceRightDerivStieltjesMeasureFamily {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)) :
    CoordinateSliceMeasureFamily n :=
  fun i y => by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        sourceRightDerivStieltjesSecondDerivativeMeasure
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) (hmono i hy)
      else
        0

/-- Source-local clamped Stieltjes slice family with the monotonicity proof supplied by ambient
convexity on `Q_3`.  This is the concrete coordinate-slice measure family intended for the
convex source proof. -/
def coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    CoordinateSliceMeasureFamily n :=
  coordinateSliceSourceRightDerivStieltjesMeasureFamily u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)

/-- Concrete convex source-local Stieltjes slices have finite mass on every bounded open
interval. -/
theorem coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily_Ioo_lt_top {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (y : SourceCubeSpace n) (a b : ℝ) :
    coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu i y
      (Set.Ioo a b) < ⊤ := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy,
      sourceRightDerivStieltjesSecondDerivativeMeasure_Ioo_lt_top]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy]

/-- Interval-average-exceeds measurability for the concrete convex Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Measurability obligation for the concrete convex source-local Stieltjes maximal bad sets.

This is the source-route analytic measurability input for the Fubini step, specialized to the
coordinate Stieltjes measure family supplied by convexity. -/
def CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceMaximalBadSetMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

namespace CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable

/-- Interval-average-exceeds measurability implies the concrete ambient coordinate maximal
bad-set measurability. -/
theorem badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (havg : CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.badSetMeasurable havg

end CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable

/-- Source mass bounds for the clamped source-local Stieltjes slices supply the abstract
coordinate-slice source mass bound used by the localized maximal argument. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hmass :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          HasSourceRightDerivStieltjesSourceMassBound
            (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
            (hmono i hy) osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc := by
  classical
  intro i y hy
  have hfamily :
      coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono i y =
        sourceRightDerivStieltjesSecondDerivativeMeasure
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) (hmono i hy) := by
    simp [coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy]
  rw [hfamily]
  exact hmass i hy

/-- Along every coordinate slice over a base in `Q_1`, the source-cube oscillation bounds all
one-dimensional value differences on the source interval `(-3,3)`. -/
theorem coordinateLine_pairwiseSub_le_sourceCubeOscillation_of_boundedOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (i : Fin n) {y : SourceCubeSpace n} (hy : y ∈ sourceOpenCube n 1)
    ⦃s r : ℝ⦄ (hs : s ∈ Set.Ioo (-3 : ℝ) 3) (hr : r ∈ Set.Ioo (-3 : ℝ) 3) :
    lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i) r -
        lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i) s ≤
      sourceCubeOscillation n u := by
  have hdomain :
      lineDomain (sourceOpenCube n 3) (coordinateLineBase i y) (sourceCoordinateVector i) =
        Set.Ioo (-3 : ℝ) 3 :=
    coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hy
  have hsQ :
      coordinateLinePoint i (coordinateLineBase i y) s ∈ sourceOpenCube n 3 := by
    have hsLine :
        s ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [hdomain] using hs
    simpa [lineDomain, coordinateLinePoint] using hsLine
  have hrQ :
      coordinateLinePoint i (coordinateLineBase i y) r ∈ sourceOpenCube n 3 := by
    have hrLine :
        r ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [hdomain] using hr
    simpa [lineDomain, coordinateLinePoint] using hrLine
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u
        (coordinateLinePoint i (coordinateLineBase i y) s) (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hsQ hbounded
  simpa [lineRestriction, coordinateLinePoint] using
    hval.2 (coordinateLinePoint i (coordinateLineBase i y) r) hrQ

/-- Ambient convexity and boundedness on `Q_3` supply the source mass bound for the concrete
convex source-local Stieltjes slice family. -/
theorem CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjes_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    CoordinateSliceSourceMassBound
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
      (sourceCubeOscillation n u) := by
  refine CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i y hy => ?_
  exact HasSourceRightDerivStieltjesSourceMassBound.of_convex_pairwise_sub_le
    (ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy)
    (sourceCubeOscillation_nonneg_of_boundedOn hbounded)
    (fun {s} {r} hs hr =>
      coordinateLine_pairwiseSub_le_sourceCubeOscillation_of_boundedOn
        (i := i) (y := y) hbounded hy (s := s) (r := r) hs hr)

end AleksandrovDifferentiability
