module

public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Core

/-!
# Compatible-frame AE slice reconstruction reductions
-/

@[expose] public noncomputable section

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

end AleksandrovDifferentiability
