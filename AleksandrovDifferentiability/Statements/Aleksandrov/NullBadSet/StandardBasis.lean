module

public import AleksandrovDifferentiability.Statements.Aleksandrov.NullBadSet.Compatible

/-!
# Standard-basis reductions to null bad sets
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Compatible null-bad-set reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleFullMeasure`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_compatibleQuotientFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Standard-basis mixed-form compatible null-bad-set reduction using non-quotient full measure
and quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_quotientReconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E)
      (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E)
      hslice hrecon

/-- Symmetric-compatible null-bad-set reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Symmetric-compatible quotient null-bad-set reduction using Mathlib's standard orthonormal
basis. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_basis_symmetricCompatibleQuotientFullMeasure
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Standard-basis mixed-strength symmetric-compatible null-bad-set reduction using non-quotient
full measure and quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_basis_symmetricFullMeasure_quotientRecon
      E Ω u (stdOrthonormalBasis ℝ E) hslice hrecon

/-- Restricted-measure compatible null-bad-set reduction using Mathlib's standard orthonormal
basis. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_compatibleFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleFullMeasure
      E Ω u hslice hrecon)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_compatibleFullMeasure`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure
      E Ω u hslice hrecon)

/-- Restricted-measure mixed-form compatible null-bad-set reduction using non-quotient full
measure and quotient reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_compatibleQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : CompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientRecon
      E Ω u hslice hrecon)

/-- Restricted-measure symmetric-compatible null-bad-set reduction using Mathlib's standard
orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_symmetricFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricFullMeasure
      E Ω u hslice hrecon)

/-- Restricted-measure symmetric-compatible quotient null-bad-set reduction using Mathlib's
standard orthonormal basis. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure
      E Ω u hslice hrecon)

/-- Restricted-measure mixed-strength symmetric-compatible null-bad-set reduction using
non-quotient full measure and quotient reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_symmetricQuotientRecon
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hslice : SymmetricCompatibleDirectionalSliceFullMeasureStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E))
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
        (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientRecon
      E Ω u hslice hrecon)

/-- Null-bad-set theorem-boundary reduction from full measure of scalar estimate loci for each
selected direction and pairwise-sum direction, plus pointwise reconstruction into polarized
ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hpure : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
        volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v
      (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineQuotientSets_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hpure : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_polarized_reconstruction
      (μ := volume) hΩ.measurableSet D v
      (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Off-diagonal version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon`: pairwise-sum line
estimates are only assumed for distinct selected directions. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hpure : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
        volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction_offDiagonal
      (μ := volume) hΩ.measurableSet D v
      (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon_offDiagonal`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineQuotientSets_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hpure : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_directionalLineQuotientSets_polarized_recon_offDiagonal
      (μ := volume) hΩ.measurableSet D v
      (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set theorem-boundary reduction from the global directional-line Fubini target plus
pointwise reconstruction into polarized ambient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj => hfubini hΩ hu (v i + v j))
    hrecon

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientSets_polarized_recon D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj => hfubini hΩ hu (v i + v j))
    hrecon

/-- Mixed-strength null-bad-set reduction: non-quotient directional-line Fubini supplies the
quotient full-measure input needed for quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon D E Ω u v
    (hfubini.quotient E) hrecon

/-- Off-diagonal bookkeeping version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj _hij => hfubini hΩ hu (v i + v j))
    hrecon

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon_offDiagonal`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj _hij => hfubini hΩ hu (v i + v j))
    hrecon

/-- Off-diagonal mixed-strength null-bad-set reduction: non-quotient directional-line Fubini
supplies the quotient full-measure input needed for quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon_offDiagonal
    D E Ω u v (hfubini.quotient E) hrecon

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon`. -/
theorem convexAleksandrovNullBadSetStatement_of_lineScalarFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon
      D E Ω u v hfubini hrecon)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_lineScalarFubini_polarized_recon`. -/
theorem convexAleksandrovNullBadSetStatement_of_lineQuotientFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon
      D E Ω u v hfubini hrecon)

/-- Restricted-measure mixed-strength null-bad-set reduction: non-quotient directional-line
Fubini supplies the quotient input needed for quotient reconstruction. -/
theorem convexAleksandrovNullBadSetStatement_of_lineScalarFubini_quotient_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon
      D E Ω u v hfubini hrecon)

/-- Restricted-measure off-diagonal version of
`convexAleksandrovNullBadSetStatement_of_lineScalarFubini_polarized_recon`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_lineScalarFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon_offDiagonal
      D E Ω u v hfubini hrecon)

/-- Restricted-measure quotient-estimate off-diagonal version of
`convexAleksandrovNullBadSetStatement_of_lineScalarFubini_polarized_recon_offDiagonal`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_lineQuotientFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon_offDiagonal
      D E Ω u v hfubini hrecon)

/-- Restricted-measure off-diagonal mixed-strength null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_lineScalarFubini_quotient_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon_offDiagonal
      D E Ω u v hfubini hrecon)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon D E Ω u v
    hfubini (hrecon hframe)

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon D E Ω u v
    hfubini (hrecon hframe)

/-- Mixed-strength null-bad-set final reduction: non-quotient directional-line Fubini may be
paired with quotient polarized reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon
    D E Ω u v hfubini (hrecon hframe)

/-- Off-diagonal bookkeeping version of
`convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_polarized_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_recon_offDiagonal`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineQuotientFubini_polarized_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Off-diagonal mixed-strength null-bad-set final reduction: non-quotient directional-line
Fubini may be paired with quotient polarized reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_lineScalarFubini_quotient_recon_offDiagonal
    D E Ω u v hfubini (hrecon hframe)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction
      D E Ω u v hframe hfubini hrecon)

/-- Restricted-measure quotient null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_quotient_fubini_and_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_reconstruction
      D E Ω u v hframe hfubini hrecon)

/-- Restricted-measure mixed-strength null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_reconstruction`. -/
theorem convexAleksandrovNullBadSetStatement_of_fubini_and_quotient_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_reconstruction
      D E Ω u v hframe hfubini hrecon)

/-- Null-bad-set theorem-boundary reduction phrased with a standard finite-indexed
orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Mixed-strength orthonormal-basis null-bad-set reduction: non-quotient directional-line Fubini
may be paired with quotient polarized reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_reconstruction
    Finset.univ E Ω u b
    (FiniteOrthonormalSpanningOn.univ_of_orthonormalBasis b) hfubini hrecon

/-- Restricted-measure null-bad-set theorem-boundary reduction phrased with a standard
finite-indexed orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_orthonormalBasis_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_reconstruction
      E Ω u b hfubini hrecon)

/-- Restricted-measure quotient null-bad-set version of
`convexAleksandrovNullBadSetStatement_of_orthonormalBasis_fubini_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction
      E Ω u b hfubini hrecon)

/-- Restricted-measure mixed-strength orthonormal-basis null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u b) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction
      E Ω u b hfubini hrecon)

/-- Null-bad-set theorem-boundary reduction using Mathlib's standard orthonormal basis. -/
theorem convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_reconstruction
      E Ω u (stdOrthonormalBasis ℝ E) hfubini hrecon

/-- Quotient-estimate null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_fubini_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotient_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_quotient_fubini_and_reconstruction
      E Ω u (stdOrthonormalBasis ℝ E) hfubini hrecon

/-- Mixed-strength standard-basis null-bad-set reduction: non-quotient directional-line Fubini
may be paired with quotient polarized reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_fubini_and_quotient_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetOnStatement_of_orthonormalBasis_fubini_and_quotient_reconstruction
      E Ω u (stdOrthonormalBasis ℝ E) hfubini hrecon

/-- Restricted-measure null-bad-set theorem-boundary reduction using Mathlib's standard
orthonormal basis. -/
theorem convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetStatement_of_fubini_and_polarized_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E)
      (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E) hfubini hrecon

/-- Restricted-measure quotient null-bad-set version of
`convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_fubini_and_reconstruction`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_quotient_fubini_and_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetStatement_of_quotient_fubini_and_polarized_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E)
      (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E) hfubini hrecon

/-- Restricted-measure mixed-strength standard-basis null-bad-set reduction. -/
theorem
    convexAleksandrovNullBadSetStatement_of_stdOrthonormalBasis_fubini_and_quotient_reconstruction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement Finset.univ E Ω u
      (stdOrthonormalBasis ℝ E)) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    convexAleksandrovNullBadSetStatement_of_fubini_and_quotient_reconstruction
      Finset.univ E Ω u (stdOrthonormalBasis ℝ E)
      (FiniteOrthonormalSpanningOn.univ_of_stdOrthonormalBasis E) hfubini hrecon

end AleksandrovDifferentiability
