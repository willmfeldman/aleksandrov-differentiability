module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.Finite

/-!
# Orthonormal-basis assembly from line estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unit-transfer a.e. reduction phrased with an arbitrary finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    htransfer hrecon

/-- Quotient-estimate unit-transfer a.e. reduction for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitSlicewiseFubiniTransfer_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    htransfer hrecon

/-- Mixed-strength unit-transfer a.e. reduction for a finite-indexed orthonormal basis: scalar
unit transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_quotient_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    htransfer hrecon

/-- Null-bad-set unit-transfer reduction for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    htransfer hrecon

/-- Quotient-estimate null-bad-set unit-transfer reduction for a finite-indexed orthonormal
basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_unitSlicewiseFubiniTransfer_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    htransfer hrecon

/-- Mixed-strength null-bad-set unit-transfer reduction for a finite-indexed orthonormal basis:
scalar unit transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
      E Ω u b htransfer hrecon)

/-- Restricted-measure unit-transfer null-bad-set reduction for a finite-indexed orthonormal
basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer
      E Ω u b htransfer hrecon)

/-- Restricted-measure quotient unit-transfer null-bad-set reduction for a finite-indexed
orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer
      E Ω u b htransfer hrecon)

/-- Restricted-measure mixed-strength unit-transfer null-bad-set reduction for a finite-indexed
orthonormal basis: scalar unit transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
      E Ω u b htransfer hrecon)

/-- A.e. reduction from canonical unit-direction good-set measurability for a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitGoodSetMeasurable_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- Quotient-estimate a.e. reduction from canonical quotient unit-direction good-set
measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitGoodSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- Mixed-strength a.e. reduction from scalar canonical unit-direction good-set measurability for
a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitGoodSetMeasurable_quotient_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- Null-bad-set reduction from canonical unit-direction good-set measurability for a
finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- Quotient null-bad-set reduction from canonical quotient unit-direction good-set
measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitGoodSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_unitGoodSetMeasurable_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- Mixed-strength null-bad-set reduction from scalar canonical unit-direction good-set
measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSetMeasurable_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_quotient_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hgood hrecon

/-- A.e. reduction from canonical unit-direction bad-set measurability for a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetMeasurable_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Quotient-estimate a.e. reduction from canonical quotient unit-direction bad-set measurability
for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitBadSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Mixed-strength a.e. reduction from scalar canonical unit-direction bad-set measurability for
a finite-indexed orthonormal basis: scalar measurability is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetMeasurable_quotient_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Null-bad-set reduction from canonical unit-direction bad-set measurability for a
finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_polarized_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Quotient null-bad-set reduction from canonical quotient unit-direction bad-set measurability
for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSetMeasurable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetMeasurable_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Mixed-strength null-bad-set reduction from scalar canonical unit-direction bad-set
measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetMeasurable_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_quotient_reconstruction
    Finset.univ E Ω u b (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b)
    hmeas hrecon

/-- Finite-transfer a.e. reduction phrased with an arbitrary finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_finiteSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient-estimate finite-transfer a.e. reduction for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-transfer a.e. reduction for a finite-indexed orthonormal basis: scalar
finite slicewise transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Null-bad-set finite-transfer reduction for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient-estimate null-bad-set finite-transfer reduction for a finite-indexed orthonormal
basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength null-bad-set finite-transfer reduction for a finite-indexed orthonormal basis:
scalar finite slicewise transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Restricted-measure finite-transfer null-bad-set reduction for a finite-indexed
orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_finiteSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteSlicewiseTransfer
      E Ω u b htransfer hrecon)

/-- Restricted-measure quotient-estimate finite-transfer null-bad-set reduction for a
finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer
      E Ω u b htransfer hrecon)

/-- Restricted-measure mixed-strength finite-transfer null-bad-set reduction for a
finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (htransfer :
      FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u b)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  convexAleksandrovNullBadSetStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    Finset.univ E Ω u b htransfer
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Finite-reconstruction a.e. reduction from canonical unit-direction good-set measurability
for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction a.e. reduction from canonical quotient unit-direction
good-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitGoodSetMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction a.e. reduction from scalar canonical unit-direction
good-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Finite-reconstruction null-bad-set reduction from canonical unit-direction good-set
measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction null-bad-set reduction from canonical quotient
unit-direction good-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitGoodSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction null-bad-set reduction from scalar canonical
unit-direction good-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSet_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
    Finset.univ E Ω u b hgood
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Finite-reconstruction a.e. reduction from canonical unit-direction bad-set measurability
for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction a.e. reduction from canonical quotient unit-direction
bad-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitBadSetMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction a.e. reduction from scalar canonical unit-direction
bad-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Finite-reconstruction null-bad-set reduction from canonical unit-direction bad-set
measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction null-bad-set reduction from canonical quotient
unit-direction bad-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction null-bad-set reduction from scalar canonical
unit-direction bad-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSet_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Restricted-measure finite-reconstruction null-bad-set reduction from canonical
unit-direction good-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitGoodSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSet_finiteRecon
      E Ω u b hgood hrecon)

/-- Restricted-measure quotient finite-reconstruction null-bad-set reduction from canonical
quotient unit-direction good-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_quotientUnitGoodSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitGoodSet_finiteRecon
      E Ω u b hgood hrecon)

/-- Restricted-measure mixed-strength finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction good-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitGoodSet_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSet_finiteQuotientRecon
      E Ω u b hgood hrecon)

/-- Restricted-measure finite-reconstruction null-bad-set reduction from canonical
unit-direction bad-set measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitBadSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSet_finiteRecon
      E Ω u b hmeas hrecon)

/-- Restricted-measure quotient finite-reconstruction null-bad-set reduction from canonical
quotient unit-direction bad-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_quotientUnitBadSet_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSet_finiteRecon
      E Ω u b hmeas hrecon)

/-- Restricted-measure mixed-strength finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction bad-set measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitBadSet_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSet_finiteQuotientRecon
      E Ω u b hmeas hrecon)

/-- Finite-reconstruction a.e. reduction from canonical unit-direction bad-set
null-measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetNullMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction a.e. reduction from canonical quotient unit-direction bad-set
null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitBadSetNullMeasurable_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction a.e. reduction from scalar canonical unit-direction
bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetNullMeasurable_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_quotient_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Finite-reconstruction null-bad-set reduction from canonical unit-direction bad-set
null-measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetNull_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finite_reconstruction
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Quotient finite-reconstruction null-bad-set reduction from canonical quotient unit-direction
bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSetNull_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotientUnitBadSetNullMeasurable_finiteRecon
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Mixed-strength finite-reconstruction null-bad-set reduction from scalar canonical
unit-direction bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetNull_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finiteQuotientRecon
    Finset.univ E Ω u b hmeas
    (hrecon (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b))

/-- Restricted-measure finite-reconstruction null-bad-set reduction from canonical
unit-direction bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitBadSetNull_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetNull_finiteRecon
      E Ω u b hmeas hrecon)

/-- Restricted-measure quotient finite-reconstruction null-bad-set reduction from canonical
quotient unit-direction bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_quotientUnitBadSetNull_finiteRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSetNull_finiteRecon
      E Ω u b hmeas hrecon)

/-- Restricted-measure mixed-strength finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction bad-set null-measurability for a finite-indexed orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_unitBadSetNull_finiteQuotientRecon
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetNull_finiteQuotientRecon
      E Ω u b hmeas hrecon)

end AleksandrovDifferentiability
