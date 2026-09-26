module

public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Compatible

/-!
# Basis AE slice reconstruction reductions
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Compatible full-measure/reconstruction reduction phrased with a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_compatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_orthonormalBasis_compatibleFullMeasure`. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Symmetric-compatible full-measure/reconstruction reduction phrased with a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_basis_symmetricCompatibleFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Symmetric-compatible quotient version of
`convexAleksandrovAEStatement_of_basis_symmetricCompatibleFullMeasure`. -/
theorem convexAleksandrovAEStatement_of_basis_symmetricCompatibleQuotientFullMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice :
      SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Mixed-strength symmetric-compatible basis reduction: non-quotient symmetric full measure is
enough when paired with symmetric-compatible quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_basis_symmetricFullMeasure_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u b)
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
        Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hslice hrecon

/-- Compatible full-measure/reconstruction reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_compatibleFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleFullMeasure`. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Standard-basis mixed-form compatible reduction using non-quotient full measure and quotient
reconstruction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleFullMeasure_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_compatibleFullMeasure_and_quotientReconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E)
      (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E)
      hslice hrecon

/-- Symmetric-compatible reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_basis_symmetricCompatibleFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Symmetric-compatible quotient reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_basis_symmetricCompatibleQuotientFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Standard-basis mixed-strength symmetric-compatible reduction using non-quotient full measure
and quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_basis_symmetricFullMeasure_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

end AleksandrovDifferentiability
