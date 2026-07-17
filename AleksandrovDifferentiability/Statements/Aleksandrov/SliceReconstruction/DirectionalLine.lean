import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Core

/-!
# Directional-line AE reconstruction reductions
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Theorem-boundary reduction from full measure of scalar estimate loci for each selected
direction and pairwise-sum direction, plus pointwise reconstruction into polarized ambient
estimates. -/
theorem convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon`. -/
theorem convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_polarized_reconstruction
    (μ := volume) hΩ.measurableSet D v (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)

/-- Off-diagonal version of
`convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon`: pairwise-sum line
estimates are only assumed for distinct selected directions. -/
theorem convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon_offDiagonal
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction_offDiagonal
      (μ := volume) hΩ.measurableSet D v (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon_offDiagonal`. -/
theorem convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon_offDiagonal
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact
    secondOrderDifferentiableAEOn_of_directionalLineQuotientSets_polarized_recon_offDiagonal
      (μ := volume) hΩ.measurableSet D v (hpure hΩ hu) (hpair hΩ hu) (hrecon hΩ hu)

/-- Theorem-boundary reduction from the global directional-line Fubini target plus pointwise
reconstruction into polarized ambient estimates. -/
theorem convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj => hfubini hΩ hu (v i + v j))
    hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon`. -/
theorem convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj => hfubini hΩ hu (v i + v j))
    hrecon

/-- Mixed-strength Fubini/reconstruction reduction: the stronger non-quotient directional-line
Fubini target supplies the quotient full-measure input needed for quotient reconstruction. -/
theorem convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_polarized_recon
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon D E Ω u v
    (hfubini.quotient E) hrecon

/-- Off-diagonal bookkeeping version of
`convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon`. -/
theorem convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineScalarSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj _hij => hfubini hΩ hu (v i + v j))
    hrecon

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_directionalLineScalarFubini_polarized_recon_offDiagonal`. -/
theorem convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientSets_polarized_recon_offDiagonal
    D E Ω u v
    (fun hΩ hu i _hi => hfubini hΩ hu (v i))
    (fun hΩ hu i _hi j _hj _hij => hfubini hΩ hu (v i + v j))
    hrecon

/-- Off-diagonal mixed-strength reduction: non-quotient directional-line Fubini supplies the
quotient full-measure input needed for quotient reconstruction. -/
theorem
    convexAleksandrovAEStatement_of_directionalLineScalarFubini_quotient_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u)
    (hrecon : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        DirectionalSliceQuotientEstimateAt D v u x →
          PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_directionalLineQuotientFubini_polarized_recon_offDiagonal
    D E Ω u v (hfubini.quotient E) hrecon

end AleksandrovDifferentiability
