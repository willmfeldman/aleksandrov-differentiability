module

public import AleksandrovDifferentiability.Statements.Aleksandrov.NullBadSet.EstimateData
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Core

/-!
# Slice-reconstruction reductions to null bad sets
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Null-bad-set theorem-boundary reduction from full measure of the finite directional slice
target plus pointwise reconstruction into mixed-directional ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_directionalSliceSet_reconstruction
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_fullMeasure_directionalSliceSet_of_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the finite directional slice
quotient target plus pointwise reconstruction into mixed-directional ambient quotient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_directionalSliceQuotientSet_reconstruction
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the finite directional slice
target plus pointwise reconstruction into polarized mixed-directional ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_directionalSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_directionalSliceSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of compatible finite directional
slice data plus pointwise reconstruction into polarized mixed-directional ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set theorem-boundary reduction from full measure of the finite directional slice
quotient target plus pointwise reconstruction into polarized quotient estimates. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_directionalSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_directionalSliceQuotientSet_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v (hslice hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set theorem-boundary reduction from restricted-a.e. membership in the finite
directional slice target plus pointwise reconstruction into mixed-directional ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_ae_directionalSliceSet_reconstruction
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ directionalSliceEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_directionalSliceSet_reconstruction
      D E Ω u v hslice hrecon)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_ae_directionalSliceSet_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_ae_directionalSliceQuotientSet_reconstruction
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ directionalSliceQuotientEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_directionalSliceQuotientSet_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of
`convexAleksandrovNullBadSetOnStatement_of_directionalSliceSet_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_ae_directionalSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ directionalSliceEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_directionalSliceSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleSliceSet_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_ae_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ compatibleDirectionalSliceEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_compatibleSliceSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of
`convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleSliceSet_polarized_reconstruction`.
-/
theorem
convexAleksandrovNullBadSetOnStatement_of_ae_symmetricCompatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ symmetricCompatibleDirectionalSliceEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        SymmetricCompatibleDirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_symmetricCompatibleSliceSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of
`convexAleksandrovNullBadSetOnStatement_of_directionalSliceQuotientSet_polarized_reconstruction`.
-/
theorem
convexAleksandrovNullBadSetOnStatement_of_ae_directionalSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ directionalSliceQuotientEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_directionalSliceQuotientSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of
`convexAleksandrovNullBadSetOnStatement_of_compatibleSliceQuotientSet_polarized_reconstruction`.
-/
theorem
    convexAleksandrovNullBadSetOnStatement_of_ae_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω, x ∈ compatibleDirectionalSliceQuotientEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        CompatibleDirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_compatibleSliceQuotientSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

/-- Null-bad-set restricted-a.e. version of the symmetric-compatible quotient reconstruction
endpoint. -/
theorem
convexAleksandrovNullBadSetOnStatement_of_ae_symmetricCompatibleSliceQuotientSet_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hslice : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂volume.restrict Ω,
        x ∈ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_ae_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
      D E Ω u v hslice hrecon)

end AleksandrovDifferentiability
