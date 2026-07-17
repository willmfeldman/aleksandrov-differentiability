import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Core

/-!
# Compatible-frame AE slice reconstruction reductions
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Theorem-boundary reduction from a full-measure compatible finite slice target plus the named
compatible polarized reconstruction statement on an orthonormal spanning family. -/
theorem convexAleksandrovAEStatement_of_compatibleSliceSet_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleSliceSet_polarized_reconstruction D E Ω u v
    hslice (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_compatibleSliceSet_and_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_compatibleSliceQuotientSet_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleSliceQuotientSet_polarized_reconstruction
    D E Ω u v hslice (hrecon hframe)

/-- Named-obligation version of
`convexAleksandrovAEStatement_of_compatibleSliceSet_and_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_compatibleFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleSliceSet_and_reconstruction
    D E Ω u v hframe hslice hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_compatibleFullMeasure_and_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleSliceQuotientSet_and_reconstruction
    D E Ω u v hframe hslice hrecon

/-- Mixed-form reduction: the stronger non-quotient compatible full-measure statement supplies
the quotient full-measure input needed for quotient-compatible reconstruction. -/
theorem convexAleksandrovAEStatement_of_compatibleFullMeasure_and_quotientReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    D E Ω u v hframe (hslice.quotient D E) hrecon

/-- Coordinate-model compatible full-measure/reconstruction reduction.  It is enough to prove
the compatible finite-slice full-measure target and compatible reconstruction after transporting
the problem through a linear isometry equivalence. -/
theorem convexAleksandrovAEStatement_of_image_compatibleFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_reconstruction D E Ω u v
    hframe
    (CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv D e hslice)
    (CompatiblePolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_image_compatibleFullMeasure_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_image_compatibleQuotientFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    D E Ω u v hframe
    (CompatibleDirectionalSliceQuotientFullMeasureStatement.of_image_linearIsometryEquiv
      D e hslice)
    (CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon)

/-- Mixed-strength coordinate-model compatible reduction: compatible non-quotient full measure in
the coordinate model is enough when paired with compatible quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_image_compatibleFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_quotientReconstruction
    D E Ω u v hframe
    (CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv D e hslice)
    (CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon)

/-- Reduction from compatible full measure and symmetric-compatible reconstruction. -/
theorem convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v
    (measure_diff_symmetricCompatibleSliceSet_eq_zero_of_compatibleSliceSet D v
      (hslice hΩ hu))
    (hrecon hframe hΩ hu)

/-- Quotient-reconstruction version of
`convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricReconstruction`. -/
theorem convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricQuotientReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v
      (measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceSet D v
        (hslice hΩ hu))
      (hrecon hframe hΩ hu)

/-- Quotient-full-measure version of
`convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricQuotientReconstruction`. -/
theorem
    convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v
      (measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
        D v (hslice hΩ hu))
      (hrecon hframe hΩ hu)

/-- Coordinate-model reduction from compatible full measure and symmetric-compatible
reconstruction. -/
theorem convexAleksandrovAEStatement_of_image_compatibleFullMeasure_symmetricReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u := by
  have hreconE :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
    exact .of_image_linearIsometryEquiv D e hrecon
  exact
    convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricReconstruction
      D E Ω u v hframe
      (CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv D e hslice)
      hreconE

/-- Coordinate-model reduction from compatible full measure and symmetric-compatible quotient
reconstruction. -/
theorem convexAleksandrovAEStatement_of_image_compatibleFullMeasure_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricQuotientReconstruction
    D E Ω u v hframe
    (CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv D e hslice)
    (symmetricCompatibleQuotientSliceRecon_of_image_linearIsometryEquiv D e hrecon)

/-- Coordinate-model reduction from compatible quotient full measure and symmetric-compatible
quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_image_compatibleQuotientFullMeasure_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
    D E Ω u v hframe
    (CompatibleDirectionalSliceQuotientFullMeasureStatement.of_image_linearIsometryEquiv
      D e hslice)
    (symmetricCompatibleQuotientSliceRecon_of_image_linearIsometryEquiv D e hrecon)

/-- Direct symmetric-compatible full-measure/reconstruction reduction. -/
theorem convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hframe hΩ hu)

/-- Direct symmetric-compatible quotient-full-measure/reconstruction reduction. -/
theorem
    convexAleksandrovAEStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hframe hΩ hu)

/-- Direct symmetric-compatible full-measure reduction paired with quotient reconstruction.
Explicit scalar estimates give their punctured quotient forms with the same symmetric data. -/
theorem convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice.quotient D E hΩ hu)
      (hrecon hframe hΩ hu)

/-- Coordinate-model direct symmetric-compatible full-measure/reconstruction reduction. -/
theorem convexAleksandrovAEStatement_of_image_symmetricCompatibleFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u := by
  have hreconE :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
    exact .of_image_linearIsometryEquiv D e hrecon
  exact
    convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_reconstruction
      D E Ω u v hframe
      (SymmetricCompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv
        D e hslice)
      hreconE

/-- Coordinate-model direct symmetric-compatible quotient full-measure/reconstruction reduction. -/
theorem
    convexAleksandrovAEStatement_of_image_symmetricCompatibleQuotientFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    D E Ω u v hframe
    (SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement.of_image_linearIsometryEquiv
      D e hslice)
    (symmetricCompatibleQuotientSliceRecon_of_image_linearIsometryEquiv D e hrecon)

/-- Coordinate-model direct symmetric-compatible full-measure reduction paired with quotient
reconstruction. -/
theorem convexAleksandrovAEStatement_of_image_symmetricCompatibleFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    D E Ω u v hframe
    (SymmetricCompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv
      D e hslice)
    (symmetricCompatibleQuotientSliceRecon_of_image_linearIsometryEquiv D e hrecon)

end AleksandrovDifferentiability
