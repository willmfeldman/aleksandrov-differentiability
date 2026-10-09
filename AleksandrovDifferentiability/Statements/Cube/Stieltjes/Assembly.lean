module

public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Controls

/-!
# Concrete Stieltjes upper-contact estimate assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

namespace ConvexUpperContactEstimateDecompositionStatement

/-- Source-route assembly theorem for the concrete convex source-local Stieltjes slice family,
with the finite-union measure constant supplied as the source-style real coefficient inequality
`(n : ℝ) * Ccoord ≤ Cmeasure`. -/
theorem of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ K₀ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hendpoint :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ K₀)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine
    of_maximalSliceControls_with_chosenConstant
      (n := n) (Cmeasure := Cmeasure) (ρ := ρ) (K₀ := K₀)
      hCmeasure_nonneg hρ hρ_le_one hK₀ ?_
  intro u t ht hbounded hu
  let μslice := coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu
  refine ⟨μslice, ?_, ?_⟩
  · exact
      (hendpoint hu hbounded).coordinateSliceOneDimEndpointControl
  · exact
      CoordinateSliceMaximalTotalBadSetEstimate.of_convexStieltjes_boundedOn_measureConstant
        (n := n) (u := u) (Cmax := Cmax) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (t := t)
        (hdiff hbounded hu) hu hbounded hmax ht
        (hfubini hu t ht hbounded) hmeasure

/-- Source-route assembly for the concrete convex source-local Stieltjes slice family.

This is the current source-faithful cube wrapper: convexity supplies the one-dimensional
Stieltjes endpoint-control input, so the remaining analytic assumptions are first differentiability
a.e., the localized maximal estimate, the Fubini estimate for the coordinate maximal bad fibers,
and the scalar finite-union constant comparison. -/
theorem of_convexSourceRightDerivStieltjes_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ) (K₀ := 2)
    hCmeasure_nonneg hρ hρ_le_one (by norm_num) hmeasure hmax hdiff
    (fun {u} hu _hbounded =>
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl.of_convex
        (u := u) (hu := hu) hρ_le_one)
    hfubini

/-- Shorter alias for the concrete convex source-local Stieltjes decomposition route. -/
theorem of_convexStieltjes_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjes_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax hdiff hfubini

/-- Concrete convex source-local Stieltjes decomposition route after discharging the
first-differentiability-a.e. input by Rademacher and local Lipschitz regularity of convex
functions.  The remaining analytic input is the coordinate Fubini estimate for the localized
maximal bad fibers. -/
theorem of_convexStieltjes_of_fubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax
    (fun {_u} _hbounded hu =>
      ConvexOn.volume_sourceOpenCube_diff_firstOrderDifferentiabilitySet_eq_zero hu)
    hfubini

/-- Concrete convex source-local Stieltjes decomposition route from the sharper transverse
Fubini boundary.  This leaves the remaining Fubini work in the source-proof form: a product
measure estimate with transverse constant `Ctrans`, plus the scalar comparison
`Ctrans * (2 * Cmax) <= Ccoord`. -/
theorem of_convexStieltjes_of_transverseFubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (htrans :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalTransverseFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              Ctrans t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_fubini_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax
    (fun {u} hu t ht hbounded =>
      (htrans (u := u) hu t ht hbounded).fubiniEstimate
        hCtrans_nonneg hfubiniConst
        (div_nonneg (sourceCubeOscillation_nonneg_of_boundedOn hbounded) ht.le))

/-- Concrete convex source-local Stieltjes decomposition route from measurability of the
coordinate maximal bad sets.  The canonical coordinate charts are already measure-preserving;
this wrapper leaves only the genuine analytic measurability obligation plus scalar constants. -/
theorem of_convexStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hbad :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_transverseFubini_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      CoordinateSliceMaximalTransverseFubiniEstimate.of_badSetMeasurable
        (hbad (u := u) hu t ht hbounded) hAmeasure)

/-- Concrete convex source-local Stieltjes decomposition route from measurability of the
interval-average-exceeds set.  This is the current sharp source-facing measurability input for
the Fubini step. -/
theorem of_convexStieltjes_of_averageExceedsMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
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
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      (havg (u := u) hu t ht hbounded).badSetMeasurable)

end ConvexUpperContactEstimateDecompositionStatement

end AleksandrovDifferentiability
