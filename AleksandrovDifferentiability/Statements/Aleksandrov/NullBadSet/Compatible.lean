module

public import AleksandrovDifferentiability.Statements.Aleksandrov.NullBadSet.SliceReconstruction
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Compatible

/-!
# Compatible-frame reductions to null bad sets
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Named-obligation null-bad-set version of compatible full-measure plus reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction
    D E Ω u v hslice (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleSliceQuotientSet_polarized_reconstruction
    D E Ω u v hslice (hrecon hframe)

/-- Mixed-form null-bad-set reduction: non-quotient compatible full measure supplies the
quotient full-measure input needed for quotient-compatible reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_quotientReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    D E Ω u v hframe (hslice.quotient D E) hrecon

/-- Restricted-measure null-bad-set version of compatible full-measure plus reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_reconstruction
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_and_reconstruction
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure mixed-form compatible null-bad-set reduction: non-quotient compatible
full measure supplies the quotient full-measure input needed for quotient-compatible
reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_quotientReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_quotientReconstruction
      D E Ω u v hframe hslice hrecon)

/-- Coordinate-model null-bad-set version of compatible full-measure plus reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_reconstruction
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleFullMeasure_reconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_compatibleQuotientFullMeasure_reconstruction
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleQuotientFullMeasure_reconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Mixed-strength coordinate-model null-bad-set reduction: compatible non-quotient full measure
in the coordinate model is enough when paired with compatible quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_quotientRecon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleFullMeasure_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model null-bad-set version of compatible full-measure plus
reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_compatibleFullMeasure_reconstruction
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_reconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_image_compatibleFullMeasure_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_compatibleQuotientFullMeasure_reconstruction
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleQuotientFullMeasure_reconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure mixed-strength coordinate-model null-bad-set reduction: compatible
non-quotient full measure in the coordinate model is enough when paired with compatible quotient
reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_compatibleFullMeasure_quotientRecon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Null-bad-set reduction from compatible full measure and symmetric-compatible reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_symmetricReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricReconstruction
      D E Ω u v hframe hslice hrecon)

/-- Null-bad-set reduction from compatible full measure and symmetric-compatible quotient
reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_compatibleFullMeasure_and_symmetricQuotientReconstruction
      D E Ω u v hframe hslice hrecon)

/-- Quotient-full-measure version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_symmetricQuotientRecon`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Coordinate-model null-bad-set reduction from compatible full measure and
symmetric-compatible reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_symmetricReconstruction
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleFullMeasure_symmetricReconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Coordinate-model null-bad-set reduction from compatible full measure and
symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_symmetricQuotientRecon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleFullMeasure_symmetricQuotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Coordinate-model null-bad-set reduction from compatible quotient full measure and
symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_compatibleQuotient_symmetricQuotientRecon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_compatibleQuotientFullMeasure_symmetricQuotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Direct null-bad-set reduction from symmetric-compatible full measure and reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_reconstruction
      D E Ω u v hframe hslice hrecon)

/-- Direct null-bad-set reduction from symmetric-compatible quotient full measure and quotient
reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Direct null-bad-set reduction from symmetric-compatible full measure and quotient
reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_quotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure null-bad-set reduction from compatible full measure and
symmetric-compatible reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_symmetricReconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_symmetricReconstruction
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure null-bad-set reduction from compatible full measure and
symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_symmetricQuotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure quotient-full-measure version of
`convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_symmetricQuotientRecon`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_symmetricQuotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure direct null-bad-set reduction from symmetric-compatible full measure and
reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_symmetricCompatibleFullMeasure_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_reconstruction
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure direct null-bad-set reduction from symmetric-compatible quotient full
measure and quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Restricted-measure direct null-bad-set reduction from symmetric-compatible full measure and
quotient reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_quotientRecon
      D E Ω u v hframe hslice hrecon)

/-- Coordinate-model direct symmetric-compatible full-measure/reconstruction null-bad-set
reduction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_symmetricCompatibleFullMeasure_recon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_symmetricCompatibleFullMeasure_reconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Coordinate-model direct symmetric-compatible quotient full-measure/reconstruction
null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_symmetricCompatibleQuotient_quotientRecon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_symmetricCompatibleQuotientFullMeasure_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Coordinate-model null-bad-set reduction from symmetric-compatible full measure and quotient
reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_symmetricFullMeasure_quotientRecon
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
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_symmetricCompatibleFullMeasure_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model null-bad-set reduction from compatible full measure and
symmetric-compatible reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_compatibleFullMeasure_symmetricReconstruction
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_symmetricReconstruction
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model null-bad-set reduction from compatible full measure and
symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_compatibleFullMeasure_symmetricQuotientRecon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleFullMeasure_symmetricQuotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model null-bad-set reduction from compatible quotient full
measure and symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_compatibleQuotient_symmetricQuotientRecon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_compatibleQuotient_symmetricQuotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model direct symmetric-compatible full-measure/reconstruction
null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_symmetricCompatibleFullMeasure_recon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_symmetricCompatibleFullMeasure_recon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model direct symmetric-compatible quotient full-measure/
reconstruction null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_symmetricCompatibleQuotient_quotientRecon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_symmetricCompatibleQuotient_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Restricted-measure coordinate-model null-bad-set reduction from symmetric-compatible full
measure and quotient reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_symmetricFullMeasure_quotientRecon
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
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_symmetricFullMeasure_quotientRecon
      D E F e Ω u v hframe hslice hrecon)

/-- Compatible null-bad-set reduction phrased with a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleFullMeasure`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Symmetric-compatible null-bad-set reduction phrased with a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Symmetric-compatible quotient null-bad-set reduction phrased with a finite-indexed
orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice :
      SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Mixed-strength symmetric-compatible basis null-bad-set reduction: non-quotient symmetric full
measure is enough when paired with symmetric-compatible quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_basis_symmetricFullMeasure_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Restricted-measure compatible null-bad-set reduction phrased with a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_compatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleFullMeasure
      E Ω u b hslice hrecon)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_orthonormalBasis_compatibleFullMeasure`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
      E Ω u b hslice hrecon)

/-- Restricted-measure mixed-form compatible null-bad-set reduction phrased with a
finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_compatibleQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  convexAleksandrovNullBadSetStatement_of_compatibleFullMeasure_and_quotientReconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Restricted-measure symmetric-compatible null-bad-set reduction phrased with a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_basis_symmetricCompatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleFullMeasure
      E Ω u b hslice hrecon)

/-- Restricted-measure symmetric-compatible quotient null-bad-set reduction phrased with a
finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_basis_symmetricCompatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice :
      SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleQuotientFullMeasure
      E Ω u b hslice hrecon)

/-- Restricted-measure mixed-strength symmetric-compatible basis null-bad-set reduction:
non-quotient symmetric full measure is enough when paired with symmetric-compatible quotient
reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_basis_symmetricFullMeasure_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_basis_symmetricFullMeasure_quotientRecon
      E Ω u b hslice hrecon)

end AleksandrovDifferentiability
