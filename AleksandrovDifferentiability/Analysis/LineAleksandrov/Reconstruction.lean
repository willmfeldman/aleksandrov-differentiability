module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.Fubini
public import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.DirectionalLine

/-!
# Reconstruction assembly from line estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Final a.e. theorem-boundary reduction from the named slicewise-to-Fubini transfer plus
pointwise polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_slicewiseFubiniTransfer_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon D E Ω u v
    (directionalLineScalarFubiniStatement_of_slicewiseToFubini htransfer) (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_slicewiseFubiniTransfer_and_polarized_reconstruction`. -/
theorem
    convexAleksandrovAEStatement_of_quotient_slicewiseFubiniTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_slicewiseToFubini htransfer)
    (hrecon hframe)

/-- Mixed-strength theorem-boundary reduction from scalar slicewise-to-Fubini transfer plus
quotient reconstruction. The scalar transfer supplies the quotient full-measure inputs through the
local-to-quotient inclusion. -/
theorem
    convexAleksandrovAEStatement_of_slicewiseFubiniTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_scalarSlicewiseToFubini htransfer)
    (hrecon hframe)

/-- Final a.e. theorem-boundary reduction from a unit-direction slicewise-to-Fubini transfer plus
pointwise polarized reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitSlicewiseToFubini htransfer) (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction`. -/
theorem
    convexAleksandrovAEStatement_of_quotient_unitSlicewiseFubiniTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_unitSlicewiseToFubini htransfer)
    (hrecon hframe)

/-- Mixed-strength theorem-boundary reduction from scalar unit-direction slicewise-to-Fubini
transfer plus quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_scalarUnitSlicewiseToFubini htransfer)
    (hrecon hframe)

/-- Null-bad-set theorem-boundary reduction from the named slicewise-to-Fubini transfer plus
pointwise polarized reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_slicewiseFubiniTransfer_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_slicewiseFubiniTransfer_and_polarized_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_slicewiseFubiniTransfer_and_polarized_reconstruction`.
-/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_slicewiseFubiniTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_quotient_slicewiseFubiniTransfer_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Mixed-strength null-bad-set theorem-boundary reduction from scalar slicewise-to-Fubini
transfer plus quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_slicewiseFubiniTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_slicewiseFubiniTransfer_quotient_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Null-bad-set theorem-boundary reduction from a unit-direction slicewise-to-Fubini transfer
plus pointwise polarized reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseFubiniTransfer_polarized_reconstruction`.
-/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitSlicewiseFubiniTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_quotient_unitSlicewiseFubiniTransfer_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Mixed-strength null-bad-set theorem-boundary reduction from scalar unit-direction
slicewise-to-Fubini transfer plus quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseFubiniTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitSlicewiseFubiniTransfer_quotient_reconstruction
      D E Ω u v hframe htransfer hrecon)

/-- Final a.e. theorem-boundary reduction from the canonical unit-direction good-set
measurability obligation plus pointwise polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitGoodSetMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitGoodSetMeasurable hgood) (hrecon hframe)

/-- Quotient-estimate theorem-boundary reduction from the canonical quotient unit-direction
good-set measurability obligation plus quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_unitGoodSetMeasurable hgood)
    (hrecon hframe)

/-- Mixed-strength theorem-boundary reduction: scalar canonical good-set measurability is enough
when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitGoodSetMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitGoodSetMeasurable hgood) (hrecon hframe)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_unitGoodSetMeasurable_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitGoodSetMeasurable_polarized_reconstruction
      D E Ω u v hframe hgood hrecon)

/-- Quotient null-bad-set version of
`convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_quotient_unitGoodSetMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_reconstruction
      D E Ω u v hframe hgood hrecon)

/-- Mixed-strength null-bad-set theorem-boundary reduction from scalar canonical good-set
measurability plus quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitGoodSetMeasurable_quotient_reconstruction
      D E Ω u v hframe hgood hrecon)

/-- Final a.e. theorem-boundary reduction from the canonical unit-direction bad-set
measurability obligation plus pointwise polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitBadSetMeasurable hmeas) (hrecon hframe)

/-- Quotient-estimate theorem-boundary reduction from the canonical quotient bad-set
measurability obligation plus quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_unitBadSetMeasurable hmeas)
    (hrecon hframe)

/-- Mixed-strength theorem-boundary reduction: scalar canonical bad-set measurability is enough
when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitBadSetMeasurable hmeas) (hrecon hframe)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_unitBadSetMeasurable_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitBadSetMeasurable_polarized_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Quotient null-bad-set version of
`convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Mixed-strength null-bad-set theorem-boundary reduction from scalar canonical bad-set
measurability plus quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitBadSetMeasurable_quotient_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Final a.e. theorem-boundary reduction from the canonical unit-direction bad-set
null-measurability obligation plus pointwise polarized reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitBadSetNullMeasurable hmeas) (hrecon hframe)

/-- Quotient-estimate theorem-boundary reduction from the canonical quotient bad-set
null-measurability obligation plus quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    D E Ω u v
    (directionalLineScalarQuotientFubiniStatement_of_unitBadSetNullMeasurable hmeas)
    (hrecon hframe)

/-- Mixed-strength theorem-boundary reduction: scalar canonical bad-set null-measurability is
enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_polarized_recon
    D E Ω u v
    (directionalLineScalarFubiniStatement_of_unitBadSetNullMeasurable hmeas) (hrecon hframe)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_polarized_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Quotient null-bad-set version of
`convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetNullMeasurable_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Mixed-strength null-bad-set theorem-boundary reduction from scalar canonical bad-set
null-measurability plus quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_quotient_reconstruction
      D E Ω u v hframe hmeas hrecon)

/-- Final a.e. theorem-boundary reduction from a finite-family slicewise-to-full-measure
transfer plus pointwise polarized reconstruction.  This is weaker than the global Fubini route:
only the selected frame directions and distinct pairwise sums are requested. -/
theorem
    convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu =>
      (htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u) hΩ hu).1)
    (fun hΩ hu =>
      (htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u) hΩ hu).2)
    hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction`. -/
theorem
    convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu =>
      (htransfer (directionalLineScalarQuotientSlicewiseStatement (E := E) Ω u) hΩ hu).1)
    (fun hΩ hu =>
      (htransfer (directionalLineScalarQuotientSlicewiseStatement (E := E) Ω u) hΩ hu).2)
    hrecon

/-- Mixed-strength finite-transfer reduction: scalar finite slicewise transfer is strong enough
to supply the quotient full-measure inputs used by quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu => (finiteDirectionalLineScalarQuotientFullMeasure_of_finiteSlicewiseTransfer
      htransfer hΩ hu).1)
    (fun hΩ hu => (finiteDirectionalLineScalarQuotientFullMeasure_of_finiteSlicewiseTransfer
      htransfer hΩ hu).2)
    hrecon

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
      D E Ω u v htransfer hrecon)

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
      D E Ω u v htransfer hrecon)

/-- Mixed-strength null-bad-set finite-transfer reduction: scalar finite slicewise transfer is
strong enough to supply the quotient full-measure inputs used by quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_finiteSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure quotient null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure mixed-strength null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
      D E Ω u v htransfer hrecon)

end AleksandrovDifferentiability
