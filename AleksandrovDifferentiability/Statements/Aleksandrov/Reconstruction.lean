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

/-- Pull a polarized reconstruction statement back from an isometric coordinate model. -/
theorem PolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : PolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    PolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' : DirectionalSliceEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      DirectionalSliceEstimateAt D (fun i ↦ e (v i)) (u ∘ e.symm) (e x) :=
    (directionalSliceEstimateAt_comp_linearIsometryEquiv (e := e)).mp hslice'
  exact PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv (e := e)
    (h hframeF hΩF huF hxF hsliceF)

/-- Pull a polarized quotient-reconstruction statement back from an isometric coordinate
model. -/
theorem PolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : PolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    PolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' : DirectionalSliceQuotientEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      DirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i)) (u ∘ e.symm) (e x) :=
    (directionalSliceQuotientEstimateAt_comp_linearIsometryEquiv (e := e)).mp hslice'
  exact PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    (e := e) (h hframeF hΩF huF hxF hsliceF)

/-- Pull a compatible polarized reconstruction statement back from an isometric coordinate
model. -/
theorem CompatiblePolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatiblePolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' : CompatibleDirectionalSliceEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      CompatibleDirectionalSliceEstimateAt D (fun i ↦ e (v i)) (u ∘ e.symm) (e x) :=
    (compatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv (e := e)).mp hslice'
  exact PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv (e := e)
    (h hframeF hΩF huF hxF hsliceF)

/-- Pull a compatible polarized quotient-reconstruction statement back from an isometric
coordinate model. -/
theorem
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' :
      CompatibleDirectionalSliceQuotientEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      CompatibleDirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i)) (u ∘ e.symm)
        (e x) :=
    (compatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv (e := e)).mp
      hslice'
  exact PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    (e := e) (h hframeF hΩF huF hxF hsliceF)

/-- Pull a symmetric-compatible polarized reconstruction statement back from an isometric
coordinate model. -/
theorem
    SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' :
      SymmetricCompatibleDirectionalSliceEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      SymmetricCompatibleDirectionalSliceEstimateAt D (fun i ↦ e (v i)) (u ∘ e.symm)
        (e x) :=
    (symmetricCompatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv (e := e)).mp
      hslice'
  exact PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv (e := e)
    (h hframeF hΩF huF hxF hsliceF)

/-- Pull a symmetric-compatible polarized quotient-reconstruction statement back from an
isometric coordinate model. -/
theorem
    symmetricCompatibleQuotientSliceRecon_of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D F
      (e '' Ω) (u ∘ e.symm) (fun i ↦ e (v i))) :
    SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  have hframeF := hframe.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hxF : e x ∈ e '' Ω := ⟨x, hx, rfl⟩
  have hslice' :
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v ((u ∘ e.symm) ∘ e) x := by
    simpa [Function.comp_def] using hslice
  have hsliceF :
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i))
        (u ∘ e.symm) (e x) :=
    (symmetricCompatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv
      (e := e)).mp hslice'
  exact PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    (e := e) (h hframeF hΩF huF hxF hsliceF)

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

/-- Symmetric-compatible reconstruction is enough for compatible reconstruction, because
compatible slice data can be symmetrized without changing the usable line data. -/
theorem symmetricSliceRecon_to_compatible
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon : SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v) :
    CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.symmetricCompatibleDirectionalSliceEstimateAt

/-- Compatible and symmetric-compatible polarized reconstruction statements are equivalent. -/
theorem compatibleSliceRecon_iff_symmetric
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E} :
    CompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v ↔
      SymmetricCompatiblePolarizedDirectionalSliceReconstructionStatement D E Ω u v :=
  ⟨compatibleSliceRecon_to_symmetric, symmetricSliceRecon_to_compatible⟩

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

/-- Symmetric-compatible quotient reconstruction is enough for compatible quotient
reconstruction, because compatible quotient-slice data can be symmetrized. -/
theorem symmetricSliceQuotientRecon_to_compatible
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hrecon :
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v) :
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v := by
  intro hframe hΩ hu x hx hslice
  exact hrecon hframe hΩ hu hx hslice.symmetricCompatibleQuotientEstimateAt

/-- Compatible and symmetric-compatible quotient polarized reconstruction statements are
equivalent. -/
theorem compatibleSliceQuotientRecon_iff_symmetric
    {ι : Type*} [DecidableEq ι] {D : Finset ι}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E} :
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v ↔
      SymmetricCompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D E Ω u v :=
  ⟨compatibleSliceQuotientRecon_to_symmetric, symmetricSliceQuotientRecon_to_compatible⟩


end AleksandrovDifferentiability
