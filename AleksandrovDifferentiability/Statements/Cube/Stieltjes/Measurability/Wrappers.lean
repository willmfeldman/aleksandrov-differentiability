module

public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Assembly
public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.CountableIntervals
public import AleksandrovDifferentiability.Statements.Cube.GoodSet

/-!
# Source-route wrappers from Stieltjes measurability reductions

This file packages the countable-interval and endpoint measurability reductions into the
source-local upper-contact estimate statement interfaces.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

open CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval

/-- Short wrapper-file name for the concrete convex Stieltjes countable-interval reverse-cover
obligation. -/
abbrev ConvexStieltjesCountableIntervalReverseCover
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
    u hu a b t

/-- Short wrapper-file name for the concrete convex Stieltjes rational-refinement obligation. -/
abbrev ConvexStieltjesAverageExceedsRationalRefinement
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement u hu t

/-- Short wrapper-file name for the concrete convex Stieltjes inner-rational-refinement
obligation. -/
abbrev ConvexStieltjesAverageExceedsInnerRationalRefinement
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement u hu t

/-- Short wrapper-file name for the concrete convex Stieltjes sequential inner-rational mass
approximation obligation. -/
abbrev ConvexStieltjesAverageExceedsInnerRationalMassTendsto
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto u hu t

/-! ## Packaged source-route wrappers from endpoint measurability -/

namespace ConvexUpperContactEstimateDecompositionStatement

/-- Concrete convex source-local Stieltjes decomposition route from a countable fixed-interval
representation of the interval-average-exceeds set. -/
theorem of_convexStieltjes_of_countableIntervals_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hfixed :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
              u hu a b t)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_averageExceedsMeasurable_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
        (hfixed (u := u) hu t ht hbounded)
        (hcover (u := u) hu t ht hbounded))

/-- Concrete convex source-local Stieltjes decomposition route from measurable fixed-interval
average maps and a countable fixed-interval representation of the interval-average-exceeds set. -/
theorem of_convexStieltjes_of_averageIntervalMaps_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (havg :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesFixedIntervalAverageMeasurable
              u hu a b)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_countableIntervals_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht _hbounded =>
      CoordinateSliceAverageExceedsCountableIntervalFamily.of_measurableAverage
        (havg (u := u) hu t ht _hbounded))
    hcover

/-- Concrete convex source-local Stieltjes decomposition route from measurable endpoint
expressions and a countable fixed-interval representation of the interval-average-exceeds set. -/
theorem of_convexStieltjes_of_endpointAverageMaps_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hend :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable
              u hu a b)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_averageIntervalMaps_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht hbounded => by
      open CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval in
      exact fixedIntervalAverageMeasurable_of_endpointAverage hab
        (hend (u := u) hu t ht hbounded))
    hcover

/-- Concrete convex source-local Stieltjes decomposition route from measurable endpoint values,
measurable endpoint left limits, and a countable fixed-interval representation of the
interval-average-exceeds set. -/
theorem of_convexStieltjes_of_endpointValueLeftLimit_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hleft :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable
              u hu b)
    (hvalue :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable
              u hu a)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_endpointAverageMaps_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    hab hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      CoordinateSliceStieltjesEndpointAverageMeasurable.of_endpointValue_leftLimit
        (hleft (u := u) hu t ht hbounded)
        (hvalue (u := u) hu t ht hbounded))
    hcover

end ConvexUpperContactEstimateDecompositionStatement

namespace ConvexUpperContactEstimateStatement

/-- Packaged upper-contact estimate from measurable endpoint values, measurable endpoint left
limits, and a countable fixed-interval representation of the concrete convex Stieltjes
interval-average-exceeds sets. -/
theorem of_convexSourceRightDerivStieltjes_of_endpointValueLeftLimit_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hleft :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable
              u hu b)
    (hvalue :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable
              u hu a)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (by
      open ConvexUpperContactEstimateDecompositionStatement in
      exact of_convexStieltjes_of_endpointValueLeftLimit_with_chosenMeasureConstant
        (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
        hab hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
        hAmeasure hfubiniConst hmax hleft hvalue hcover)

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
proved in this file and a countable fixed-interval representation of the interval-average
exceeds sets. -/
theorem of_convexSourceRightDerivStieltjes_of_countableIntervalCover_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hcover :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
              u hu a b t) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_endpointValueLeftLimit_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    hab hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg hAmeasure
    hfubiniConst hmax
    (fun ⦃u⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (_t : ℝ) (_ht : 0 < _t)
        (_hbdd : BoundedOn (sourceOpenCube n 3) u) =>
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_convex
        (u := u) (hu := hu) (b := b))
    (fun ⦃u⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (_t : ℝ) (_ht : 0 < _t)
        (_hbdd : BoundedOn (sourceOpenCube n 3) u) =>
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_convex
        (u := u) (hu := hu) (a := a))
    hcover

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
proved in this file and the reverse-cover direction for a countable fixed-interval family. -/
theorem
    of_convexSourceRightDerivStieltjes_of_countableIntervalReverseCover_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hreverse :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexStieltjesCountableIntervalReverseCover u hu a b t) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_countableIntervalCover_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    (fun k => (hadm k).1)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg hAmeasure
    hfubiniConst hmax
    (fun ⦃u⦄ hu t ht hbounded => by
      exact cover_of_reverseCover hadm (hreverse (u := u) hu t ht hbounded))

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
proved in this file and rational refinement of source-local average witnesses. -/
theorem of_convexSourceRightDerivStieltjes_of_rationalRefinement_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hrefine :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexStieltjesAverageExceedsRationalRefinement u hu t) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_countableIntervalReverseCover_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    henum.admissible hCmeasure_nonneg hρ hρ_le_one hmeasure
    hCtrans_nonneg hAmeasure hfubiniConst hmax
    (fun ⦃u⦄ hu t ht hbounded =>
      reverseCover_of_rationalRefinement henum
        (hrefine (u := u) hu t ht hbounded))

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
proved in this file and inner-rational refinement of source-local average witnesses. -/
theorem
    of_convexSourceRightDerivStieltjes_of_innerRationalRefinement_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hrefine :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexStieltjesAverageExceedsInnerRationalRefinement u hu t) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_rationalRefinement_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    henum hCmeasure_nonneg hρ hρ_le_one hmeasure
    hCtrans_nonneg hAmeasure hfubiniConst hmax
    (fun ⦃u⦄ hu t ht hbounded =>
      rationalRefinement_of_inner (hrefine (u := u) hu t ht hbounded))

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
proved in this file and sequential inner-rational mass approximation. -/
theorem
    of_convexSourceRightDerivStieltjes_of_innerRationalMassTendsto_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hmassApprox :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexStieltjesAverageExceedsInnerRationalMassTendsto u hu t) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_innerRationalRefinement_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    henum hCmeasure_nonneg hρ hρ_le_one hmeasure
    hCtrans_nonneg hAmeasure hfubiniConst hmax
    (fun ⦃u⦄ hu t ht hbounded =>
      innerRationalRefinement_of_massTendsto
        (hmassApprox (u := u) hu t ht hbounded))

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability,
the automatic inner-rational mass approximation, and a rational interval enumeration. -/
theorem of_convexSourceRightDerivStieltjes_of_rationalEnumeration_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ} {a b : ℕ → ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax) :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_innerRationalMassTendsto_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    henum hCmeasure_nonneg hρ hρ_le_one hmeasure
    hCtrans_nonneg hAmeasure hfubiniConst hmax
    (fun ⦃u⦄ hu t _ht _hbounded =>
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto.of_convex
        u hu t)

/-- Packaged upper-contact estimate from the concrete convex Stieltjes endpoint measurability
and automatic enumeration of all rational source-admissible intervals. -/
theorem
    of_convexSourceRightDerivStieltjes_of_existsRationalEnumeration_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax) :
    ConvexUpperContactEstimateStatement n := by
  rcases exists_sourceRationalIntervalEnumeration with ⟨a, b, henum⟩
  exact of_convexSourceRightDerivStieltjes_of_rationalEnumeration_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ) (a := a) (b := b)
    henum hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax

/-- Packaged upper-contact estimate from the concrete convex Stieltjes route after choosing the
transverse and finite-union scalar constants internally.  The only remaining analytic input at
this boundary is the source-local one-dimensional maximal estimate. -/
theorem of_convexSourceRightDerivStieltjes_of_localizedMaximal
    {n : ℕ} {Cmax : ℝ} (hmax : LocalizedMaximalEstimateStatement Cmax) :
    ConvexUpperContactEstimateStatement n := by
  rcases exists_nonneg_forall_sourceTransverseOpenCube_volume_le_ofReal (n := n) with
    ⟨Ctrans, hCtrans_nonneg, hAmeasure⟩
  let Ccoord : ℝ := Ctrans * (2 * Cmax)
  let Cmeasure : ℝ := (n : ℝ) * Ccoord
  have hCcoord_nonneg : 0 ≤ Ccoord := by
    dsimp [Ccoord]
    exact mul_nonneg hCtrans_nonneg (mul_nonneg (by norm_num) hmax.1)
  have hCmeasure_nonneg : 0 ≤ Cmeasure := by
    dsimp [Cmeasure]
    exact mul_nonneg (Nat.cast_nonneg n) hCcoord_nonneg
  have hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure := by
    dsimp [Cmeasure]
    exact le_rfl
  have hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord := by
    dsimp [Ccoord]
    exact le_rfl
  exact
    of_convexSourceRightDerivStieltjes_of_existsRationalEnumeration_with_chosenMeasureConstant
      (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
      (Cmeasure := Cmeasure) (ρ := 1)
      hCmeasure_nonneg (by norm_num) (by norm_num) hmeasure hCtrans_nonneg hAmeasure
      hfubiniConst hmax

/-- Packaged upper-contact estimate from the existential source-local one-dimensional maximal
estimate.  This is the source-facing boundary after the concrete Stieltjes, measurability,
enumeration, transverse-volume, and scalar-constant bookkeeping has been discharged. -/
theorem of_convexSourceRightDerivStieltjes_of_existsLocalizedMaximal
    {n : ℕ} (hmax : ExistsLocalizedMaximalEstimateStatement) :
    ConvexUpperContactEstimateStatement n := by
  rcases hmax with ⟨Cmax, hCmax⟩
  exact of_convexSourceRightDerivStieltjes_of_localizedMaximal
    (n := n) (Cmax := Cmax) hCmax

/-- Packaged upper-contact estimate from the concrete convex Stieltjes route and the proved
source-local one-dimensional maximal estimate. -/
theorem of_convexSourceRightDerivStieltjes
    {n : ℕ} :
    ConvexUpperContactEstimateStatement n :=
  of_convexSourceRightDerivStieltjes_of_existsLocalizedMaximal
    (n := n) existsLocalizedMaximalEstimateStatement

end ConvexUpperContactEstimateStatement

/-- Finite upper-contact opening a.e. on the source cube from the concrete convex Stieltjes
upper-contact estimate. -/
theorem ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_convexSourceRightDerivStieltjes
    {n : ℕ} :
    ConvexFiniteUpperContactOpeningAEOnCubeStatement n :=
  ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_upperContactEstimate
    (ConvexUpperContactEstimateStatement.of_convexSourceRightDerivStieltjes (n := n))

end AleksandrovDifferentiability
