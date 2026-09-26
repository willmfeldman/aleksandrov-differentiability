module

public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.DirectionalLine

/-!
# Fubini AE reconstruction reductions
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Final theorem-boundary reduction from the two named finite-dimensional slicing obligations:
the global directional-line Fubini statement and pointwise polarized reconstruction on a finite
orthonormal spanning family. -/
theorem convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon D E Ω u v
    hfubini (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_quotient_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon D E Ω u v
    hfubini (hrecon hframe)

/-- Mixed-strength final reduction: a non-quotient directional-line Fubini statement may be paired
with quotient polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_fubini_and_quotient_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_polarized_recon
    D E Ω u v hfubini (hrecon hframe)

/-- Off-diagonal bookkeeping version of
`convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_fubini_and_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_fubini_and_polarized_recon_offDiagonal`. -/
theorem convexAleksandrovAEStatement_of_quotient_fubini_and_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Off-diagonal mixed-strength final reduction: non-quotient directional-line Fubini may be
paired with quotient polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_fubini_and_quotient_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Final theorem-boundary reduction phrased with a standard finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_orthonormalBasis_fubini_and_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_fubini_and_polarized_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Mixed-strength orthonormal-basis reduction: non-quotient directional-line Fubini may be
paired with quotient polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fubini_and_quotient_polarized_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Final theorem-boundary reduction using Mathlib's standard orthonormal basis for a
finite-dimensional real inner product space. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_fubini_and_reconstruction E Ω u
      (stdOrthonormalBasis ℝ E) hfubini hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_stdOrthonormalBasis_fubini_and_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_quotient_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction E Ω u
      (stdOrthonormalBasis ℝ E) hfubini hrecon

/-- Mixed-strength standard-basis reduction: non-quotient directional-line Fubini may be paired
with quotient polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_fubini_and_quotient_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction E Ω u
      (stdOrthonormalBasis ℝ E) hfubini hrecon


end AleksandrovDifferentiability
