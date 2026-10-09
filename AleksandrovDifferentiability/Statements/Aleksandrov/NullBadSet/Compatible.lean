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

end AleksandrovDifferentiability
