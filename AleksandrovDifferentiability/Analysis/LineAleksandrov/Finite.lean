module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.Reconstruction

/-!
# Finite reconstruction assembly from line estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite-reconstruction a.e. reduction from a unit-direction slicewise-to-Fubini transfer. -/
theorem convexAleksandrovAEStatement_of_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini htransfer)
    hrecon

/-- Quotient finite-reconstruction a.e. reduction from a quotient unit-direction
slicewise-to-Fubini transfer. -/
theorem convexAleksandrovAEStatement_of_quotient_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
      htransfer)
    hrecon

/-- Mixed-strength finite-reconstruction a.e. reduction: scalar unit-direction transfer is
enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitSlicewiseTransfer_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu =>
      (finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
        (D := D) (v := v) htransfer hΩ hu).1)
    (fun hΩ hu =>
      (finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
        (D := D) (v := v) htransfer hΩ hu).2)
    hrecon

/-- Null-bad-set finite-reconstruction reduction from a unit-direction slicewise-to-Fubini
transfer. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini htransfer)
    hrecon

/-- Quotient null-bad-set finite-reconstruction reduction from a quotient unit-direction
slicewise-to-Fubini transfer. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
      htransfer)
    hrecon

/-- Mixed-strength null-bad-set finite-reconstruction reduction: scalar unit-direction transfer is
enough when paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseTransfer_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  ConvexAleksandrovAEStatement.nullBadSetOnStatement E
    (convexAleksandrovAEStatement_of_unitSlicewiseTransfer_finite_quotient_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure finite-reconstruction null-bad-set reduction from a unit-direction
slicewise-to-Fubini transfer. -/
theorem convexAleksandrovNullBadSetStatement_of_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseTransfer_finite_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure quotient finite-reconstruction null-bad-set reduction from a quotient
unit-direction slicewise-to-Fubini transfer. -/
theorem
    convexAleksandrovNullBadSetStatement_of_quotient_unitSlicewiseTransfer_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_quotient_unitSlicewiseTransfer_finite_reconstruction
      D E Ω u v htransfer hrecon)

/-- Restricted-measure mixed-strength finite-reconstruction null-bad-set reduction: scalar
unit-direction transfer is enough when paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_unitSlicewiseTransfer_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_unitSlicewiseTransfer_finite_quotient_reconstruction
      D E Ω u v htransfer hrecon)

/-- Finite-reconstruction a.e. reduction from the canonical scalar unit-direction good-set
measurability obligation. -/
theorem convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Quotient finite-reconstruction a.e. reduction from the canonical quotient unit-direction
good-set measurability obligation. -/
theorem convexAleksandrovAEStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Mixed-strength finite-reconstruction a.e. reduction: scalar canonical good-set measurability
is enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Null-bad-set finite-reconstruction reduction from the canonical scalar unit-direction
good-set measurability obligation. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Quotient null-bad-set finite-reconstruction reduction from the canonical quotient
unit-direction good-set measurability obligation. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitGoodSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Mixed-strength null-bad-set finite-reconstruction reduction: scalar canonical good-set
measurability is enough when paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitGoodSetMeasurable_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable hgood)
    hrecon

/-- Finite-reconstruction a.e. reduction from the canonical scalar unit-direction bad-set
measurability obligation. -/
theorem convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Quotient finite-reconstruction a.e. reduction from the canonical quotient unit-direction
bad-set measurability obligation. -/
theorem convexAleksandrovAEStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Mixed-strength finite-reconstruction a.e. reduction: scalar canonical bad-set measurability
is enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Null-bad-set finite-reconstruction reduction from the canonical scalar unit-direction
bad-set measurability obligation. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Quotient null-bad-set finite-reconstruction reduction from the canonical quotient
unit-direction bad-set measurability obligation. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_unitBadSetMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Mixed-strength null-bad-set finite-reconstruction reduction: scalar canonical bad-set
measurability is enough when paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetMeasurable_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable hmeas)
    hrecon

/-- Finite-reconstruction a.e. reduction from the canonical scalar unit-direction bad-set
null-measurability obligation. -/
theorem convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Quotient finite-reconstruction a.e. reduction from the canonical quotient unit-direction
bad-set null-measurability obligation. -/
theorem convexAleksandrovAEStatement_of_quotient_unitBadSetNullMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Mixed-strength finite-reconstruction a.e. reduction: scalar canonical bad-set
null-measurability is enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_unitBadSetNullMeasurable_finite_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Null-bad-set finite-reconstruction reduction from the canonical scalar unit-direction
bad-set null-measurability obligation. -/
theorem convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finite_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Quotient null-bad-set finite-reconstruction reduction from the canonical quotient
unit-direction bad-set null-measurability obligation. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotientUnitBadSetNullMeasurable_finiteRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Mixed-strength null-bad-set finite-reconstruction reduction: scalar canonical bad-set
null-measurability is enough when paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_unitBadSetNullMeasurable_finiteQuotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable hmeas)
    hrecon

/-- Coordinate-model finite-transfer a.e. reduction.  It is enough to prove the finite scalar
transfer and polarized reconstruction after transporting the domain, function, and finite frame
through a linear isometry equivalence. -/
theorem convexAleksandrovAEStatement_of_image_finiteSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_polarized_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv D e hrecon)
      hframe)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_image_finiteSlicewiseTransfer_reconstruction`. -/
theorem convexAleksandrovAEStatement_of_image_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D F (e '' Ω)
        (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

/-- Mixed-strength coordinate-model finite-transfer a.e. reduction: scalar finite transfer in
the coordinate model is enough when paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_image_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

/-- Coordinate-model finite-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_finiteSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv D e hrecon)
      hframe)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_image_finiteSlicewiseTransfer_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_image_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D F (e '' Ω)
        (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

/-- Mixed-strength coordinate-model finite-transfer null-bad-set reduction: scalar finite
transfer in the coordinate model is enough when paired with quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

/-- Restricted-measure coordinate-model finite-transfer null-bad-set reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_finiteSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  convexAleksandrovNullBadSetStatement_of_finiteSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv D e hrecon)
      hframe)

/-- Restricted-measure quotient-estimate coordinate-model finite-transfer null-bad-set
reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_image_finiteQuotientSlicewiseTransfer_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer :
      FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D F (e '' Ω)
        (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  convexAleksandrovNullBadSetStatement_of_finiteQuotientSlicewiseTransfer_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

/-- Restricted-measure mixed-strength coordinate-model finite-transfer null-bad-set
reduction. -/
theorem convexAleksandrovNullBadSetStatement_of_image_finiteSlicewiseTransfer_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i)))
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  convexAleksandrovNullBadSetStatement_of_finiteSlicewiseTransfer_quotient_reconstruction
    D E Ω u v
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
      D e htransfer)
    ((PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
      D e hrecon) hframe)

end AleksandrovDifferentiability
