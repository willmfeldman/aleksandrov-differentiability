module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.OrthonormalBasis

/-!
# Standard-basis assembly from line estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Standard-basis unit-transfer a.e. reduction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Quotient-estimate standard-basis unit-transfer a.e. reduction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_quotientUnitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Mixed-strength standard-basis unit-transfer a.e. reduction: scalar unit transfer is enough
for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitSlicewiseTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Standard-basis unit-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Quotient-estimate standard-basis unit-transfer null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotientUnitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitSlicewiseTransfer
      E Ω u (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Mixed-strength standard-basis unit-transfer null-bad-set reduction: scalar unit transfer is
enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitSlicewiseTransfer_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Restricted-measure standard-basis unit-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_unitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitSlicewiseTransfer
      E Ω u htransfer hrecon)

/-- Restricted-measure quotient standard-basis unit-transfer null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_quotientUnitSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotientUnitSlicewiseTransfer
      E Ω u htransfer hrecon)

/-- Restricted-measure mixed-strength standard-basis unit-transfer null-bad-set reduction:
scalar unit transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_unitTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitTransfer_quotientRecon
      E Ω u htransfer hrecon)

/-- Standard-basis a.e. reduction from canonical unit-direction good-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitGoodSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Quotient-estimate standard-basis a.e. reduction from canonical quotient unit-direction
good-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_quotientUnitGoodSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitGoodSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Mixed-strength standard-basis a.e. reduction from scalar canonical unit-direction good-set
measurability: scalar good-set measurability is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitGoodSetMeasurable_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitGoodSetMeasurable_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Standard-basis null-bad-set reduction from canonical unit-direction good-set measurability. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitGoodSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Quotient-estimate standard-basis null-bad-set reduction from canonical quotient
unit-direction good-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotientUnitGoodSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitGoodSetMeasurable
      E Ω u (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Mixed-strength standard-basis null-bad-set reduction from scalar canonical unit-direction
good-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitGoodSetMeasurable_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitGoodSetMeasurable_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hgood hrecon

/-- Standard-basis a.e. reduction from canonical unit-direction bad-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitBadSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Quotient-estimate standard-basis a.e. reduction from canonical quotient unit-direction
bad-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_quotientUnitBadSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_quotientUnitBadSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Mixed-strength standard-basis a.e. reduction from scalar canonical unit-direction bad-set
measurability: scalar measurability is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_stdOrthonormalBasis_unitBadSetMeasurable_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_unitBadSetMeasurable_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Standard-basis null-bad-set reduction from canonical unit-direction bad-set measurability. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitBadSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetMeasurable E Ω u
      (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Quotient-estimate standard-basis null-bad-set reduction from canonical quotient
unit-direction bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotientUnitBadSetMeasurable
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotientUnitBadSetMeasurable
      E Ω u (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Mixed-strength standard-basis null-bad-set reduction from scalar canonical unit-direction
bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_unitBadSetMeasurable_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_unitBadSetMeasurable_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hmeas hrecon

/-- Standard-basis finite-transfer a.e. reduction. -/
theorem convexAleksandrovAEStatement_of_stdOrthonormalBasis_finiteSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_finiteSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Quotient-estimate standard-basis finite-transfer a.e. reduction. -/
theorem
    convexAleksandrovAEStatement_of_stdOrthonormalBasis_finiteQuotientSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Mixed-strength standard-basis finite-transfer a.e. reduction: scalar finite slicewise
transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_stdOrthonormalBasis_finiteSlicewiseTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_orthonormalBasis_finiteSlicewiseTransfer_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Standard-basis finite-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteSlicewiseTransfer E Ω u
      (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Quotient-estimate standard-basis finite-transfer null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteQuotientSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteQuotientSlicewiseTransfer
      E Ω u (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Mixed-strength standard-basis finite-transfer null-bad-set reduction: scalar finite
slicewise transfer is enough for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_finiteSlicewiseTransfer_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) htransfer hrecon

/-- Restricted-measure standard-basis finite-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_finiteSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteSlicewiseTransfer
      E Ω u htransfer hrecon)

/-- Restricted-measure quotient-estimate standard-basis finite-transfer null-bad-set
reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_finiteQuotientSlicewiseTransfer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteQuotientSlicewiseTransfer
      E Ω u htransfer hrecon)

/-- Restricted-measure mixed-strength standard-basis finite-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_finiteTransfer_quotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_finiteTransfer_quotientRecon
      E Ω u htransfer hrecon)

/-- Standard-basis finite-reconstruction a.e. reduction from canonical unit-direction good-set
measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction a.e. reduction from canonical quotient
unit-direction good-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_quotientUnitGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction a.e. reduction from scalar canonical
unit-direction good-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitGoodSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Standard-basis finite-reconstruction null-bad-set reduction from canonical unit-direction
good-set measurability. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction null-bad-set reduction from canonical quotient
unit-direction good-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction good-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitGoodSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hgood
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Standard-basis finite-reconstruction a.e. reduction from canonical unit-direction bad-set
measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction a.e. reduction from canonical quotient
unit-direction bad-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_quotientUnitBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction a.e. reduction from scalar canonical
unit-direction bad-set measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitBadSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Standard-basis finite-reconstruction null-bad-set reduction from canonical unit-direction
bad-set measurability. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction null-bad-set reduction from canonical quotient
unit-direction bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Restricted-measure standard-basis finite-reconstruction null-bad-set reduction from
canonical unit-direction good-set measurability. -/
theorem convexAleksandrovNullBadSetStatement_of_stdBasis_unitGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitGoodSetMeasurable_finiteRecon
      E Ω u hgood hrecon)

/-- Restricted-measure quotient standard-basis finite-reconstruction null-bad-set reduction from
canonical quotient unit-direction good-set measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_quotientGoodSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientGoodSetMeasurable_finiteRecon
      E Ω u hgood hrecon)

/-- Restricted-measure mixed-strength standard-basis finite-reconstruction null-bad-set
reduction from scalar canonical unit-direction good-set measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_unitGoodSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitGoodSetMeasurable_finiteQuotientRecon
      E Ω u hgood hrecon)

/-- Restricted-measure standard-basis finite-reconstruction null-bad-set reduction from
canonical unit-direction bad-set measurability. -/
theorem convexAleksandrovNullBadSetStatement_of_stdBasis_unitBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetMeasurable_finiteRecon
      E Ω u hmeas hrecon)

/-- Restricted-measure quotient standard-basis finite-reconstruction null-bad-set reduction from
canonical quotient unit-direction bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_quotientBadSetMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientBadSetMeasurable_finiteRecon
      E Ω u hmeas hrecon)

/-- Restricted-measure mixed-strength standard-basis finite-reconstruction null-bad-set
reduction from scalar canonical unit-direction bad-set measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_unitBadSetMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetMeasurable_finiteQuotientRecon
      E Ω u hmeas hrecon)

/-- Standard-basis finite-reconstruction a.e. reduction from canonical unit-direction bad-set
null-measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction a.e. reduction from canonical quotient
unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovAEStatement_of_stdBasis_quotientUnitBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction a.e. reduction from scalar canonical
unit-direction bad-set null-measurability. -/
theorem convexAleksandrovAEStatement_of_stdBasis_unitBadSetNullMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovAEStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Standard-basis finite-reconstruction null-bad-set reduction from canonical unit-direction
bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finite_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Quotient standard-basis finite-reconstruction null-bad-set reduction from canonical quotient
unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_quotientUnitBadSetNullMeasurable_finiteRecon
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Mixed-strength standard-basis finite-reconstruction null-bad-set reduction from scalar
canonical unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetNullMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finiteQuotientRecon
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E) hmeas
      (hrecon (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E))

/-- Restricted-measure standard-basis finite-reconstruction null-bad-set reduction from
canonical unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_unitBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetNullMeasurable_finiteRecon
      E Ω u hmeas hrecon)

/-- Restricted-measure quotient standard-basis finite-reconstruction null-bad-set reduction from
canonical quotient unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_quotientBadSetNullMeasurable_finiteRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_quotientBadSetNullMeasurable_finiteRecon
      E Ω u hmeas hrecon)

/-- Restricted-measure mixed-strength standard-basis finite-reconstruction null-bad-set reduction
from scalar canonical unit-direction bad-set null-measurability. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdBasis_unitBadSetNullMeasurable_finiteQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdBasis_unitBadSetNullMeasurable_finiteQuotientRecon
      E Ω u hmeas hrecon)


end AleksandrovDifferentiability
