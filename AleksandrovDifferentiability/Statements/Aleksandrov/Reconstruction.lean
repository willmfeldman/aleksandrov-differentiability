module

public import AleksandrovDifferentiability.Statements.Aleksandrov.Transport

/-!
# Reconstruction statement interfaces
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Pointwise reconstruction target for the finite-dimensional proof: finite slice estimates in
an orthonormal spanning family and its pairwise sums reconstruct an ambient polarized quadratic
estimate. -/
def PolarizedDirectionalSliceReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x

/-- Pointwise reconstruction target with compatible first-order slice data.  This stronger
version exposes the common ambient affine slope needed to reconstruct an ambient second-order
expansion from finite one-dimensional Taylor data. -/
def CompatiblePolarizedDirectionalSliceReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      CompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x

/-- Pointwise reconstruction target from symmetric compatible first-order slice data.  This is
often the most natural finite algebra target, because the pairwise-sum coefficients have already
been symmetrized on the finite frame. -/
def SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      SymmetricCompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x

/-- Punctured normalized quotient version of
`PolarizedDirectionalSliceReconstructionStatement`. -/
def PolarizedDirectionalSliceQuotientReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x

/-- Punctured normalized quotient version of
`CompatiblePolarizedDirectionalSliceReconstructionStatement`. -/
def CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x

/-- Punctured normalized quotient version of
`SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement`. -/
def SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  FiniteOrthonormalSpanningOn D v → IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ⦃x : E⦄, x ∈ Ω →
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- A reconstruction theorem for arbitrary finite directional slice data also applies to the
compatible finite-slice target. -/
theorem polarizedSliceRecon_to_compatible
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon : PolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.directionalSliceEstimateAt

/-- Compatible reconstruction also applies to symmetric-compatible finite-slice data. -/
theorem compatibleSliceRecon_to_symmetric
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon : CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.compatibleDirectionalSliceEstimateAt

/-- A quotient reconstruction theorem for arbitrary finite directional slice data also applies
to the compatible finite quotient-slice target. -/
theorem polarizedSliceQuotientRecon_to_compatible
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon : PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.directionalSliceQuotientEstimateAt

/-- Compatible quotient reconstruction also applies to symmetric-compatible finite quotient-slice
data. -/
theorem compatibleSliceQuotientRecon_to_symmetric
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.compatibleQuotientEstimateAt

end AleksandrovDifferentiability
