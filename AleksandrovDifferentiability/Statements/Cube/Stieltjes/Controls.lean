module

public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Basic

/-!
# Concrete Stieltjes endpoint and mass controls
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

def CoordinateSliceSourceRightDerivStieltjesEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ K : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointControl
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ K

/-- Exact endpoint identities for the clamped source-local right-derivative Stieltjes slices. -/
def CoordinateSliceSourceRightDerivStieltjesEndpointIdentities {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointIdentities
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ

/-- Endpoint comparison bounds for the clamped source-local right-derivative Stieltjes slices. -/
def CoordinateSliceSourceRightDerivStieltjesEndpointBounds {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointBounds
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ

/-- Exact endpoint identities imply endpoint comparison bounds slicewise. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointIdentities.endpointBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hident : CoordinateSliceSourceRightDerivStieltjesEndpointIdentities u hmono ρ) :
    CoordinateSliceSourceRightDerivStieltjesEndpointBounds u hmono ρ := by
  intro x hx hdiff i
  exact (hident hx hdiff i).endpointBounds

/-- Slice-level endpoint comparisons imply slice-level endpoint control with constant `2`, provided
the coordinate slices are convex on the source interval. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointBounds.endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hbounds : CoordinateSliceSourceRightDerivStieltjesEndpointBounds u hmono ρ)
    (hconv :
      ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
        DifferentiableAt ℝ u x →
          ∀ i : Fin n,
            ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3)
              (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i)))
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceSourceRightDerivStieltjesEndpointControl u hmono ρ 2 := by
  intro x hx hdiff i
  exact HasSourceRightDerivStieltjesEndpointControl.of_endpointBounds
    (hbounds hx hdiff i) (hconv hx hdiff i) hρ_le_one

/-- Endpoint control for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ K : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointControl u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ K

/-- Exact endpoint identities for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointIdentities u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ

/-- Endpoint comparison bounds for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointBounds u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities

/-- Ambient convexity supplies the concrete slicewise endpoint identities. -/
theorem of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities u hu ρ := by
  intro x hx _hdiff i
  exact HasSourceRightDerivStieltjesEndpointIdentities.of_convex hρ_le_one
    (ConvexOn.coordinateLineRestriction_sourceCube_three hu i hx)

/-- Concrete convex endpoint identities imply concrete endpoint comparison bounds. -/
theorem endpointBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ}
    (hident : CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities u hu ρ) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds u hu ρ :=
  CoordinateSliceSourceRightDerivStieltjesEndpointIdentities.endpointBounds
    (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hident

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds

/-- Concrete convex endpoint comparisons imply concrete endpoint control with constant `2`. -/
theorem endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ}
    (hbounds : CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds u hu ρ)
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ 2 :=
  CoordinateSliceSourceRightDerivStieltjesEndpointBounds.endpointControl
    (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hbounds
    (fun {_} hx _hdiff i => ConvexOn.coordinateLineRestriction_sourceCube_three hu i hx)
    hρ_le_one

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds

/-- The clamped source-local Stieltjes endpoint input implies the abstract one-dimensional
endpoint-control input expected by `Cube.Maximal`. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointControl.coordinateSliceOneDimEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ K : ℝ}
    (hendpoint : CoordinateSliceSourceRightDerivStieltjesEndpointControl u hmono ρ K) :
    CoordinateSliceOneDimEndpointControl u
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) ρ K := by
  classical
  intro x hx hdiff i
  have hbase : coordinateLineBase i x ∈ sourceOpenCube n 1 :=
    coordinateLineBase_mem_sourceOpenCube_one (i := i) hx
  have hbase_idem : coordinateLineBase i (coordinateLineBase i x) = coordinateLineBase i x :=
    coordinateLineBase_idem i x
  simpa [CoordinateSliceSourceRightDerivStieltjesEndpointControl,
    HasSourceRightDerivStieltjesEndpointControl,
    coordinateSliceSourceRightDerivStieltjesMeasureFamily, hbase, hbase_idem]
    using hendpoint hx hdiff i

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl

/-- Ambient convexity supplies concrete slicewise endpoint control with constant `2`. -/
theorem of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ 2 :=
  (CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities.endpointBounds
      (CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities.of_convex
        (u := u) (hu := hu) hρ_le_one)).endpointControl hρ_le_one

/-- The concrete convex source-local Stieltjes endpoint input implies the abstract
one-dimensional endpoint-control input expected by `Cube.Maximal`. -/
theorem coordinateSliceOneDimEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ K : ℝ}
    (hendpoint : CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ K) :
    CoordinateSliceOneDimEndpointControl u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) ρ K := by
  exact CoordinateSliceSourceRightDerivStieltjesEndpointControl.coordinateSliceOneDimEndpointControl
    (n := n) (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hendpoint

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl

/-- Total bad-set estimate for the concrete convex source-local Stieltjes slice family from
ambient convexity, boundedness, the localized maximal theorem, and the Fubini bookkeeping, with
the finite-union constant supplied as a real coefficient inequality. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_convexStieltjes_boundedOn_measureConstant
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
        (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure) :
    CoordinateSliceMaximalTotalBadSetEstimate u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate_of_measureConstant
    hdiff
    (CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjes_boundedOn hu hbounded)
    hmax ht hfubini hmeasure hbounded

end AleksandrovDifferentiability
