module

public import AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic

/-!
# Ambient quadratic estimates

Ambient quadratic remainder estimate predicates and their connection to second-order expansions.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second-order expansion predicate can be read as a quadratic expansion of the affine
remainder after subtracting the first-order slope. -/
theorem hasSecondOrderExpansionAt_iff_affineRemainder
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E} :
    HasSecondOrderExpansionAt u x p B ↔
      (fun z : E =>
          affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
        =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  rw [HasSecondOrderExpansionAt]
  simp only [affineRemainder, add_sub_cancel_left]
  have hfun :
      (fun z : E =>
          u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z)) =
        (fun z : E =>
          u (x + z) - (u x + inner ℝ p z) - (1 / 2 : ℝ) * inner ℝ z (B z)) := by
    funext z
    ring
  rw [hfun]

theorem hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h :
      (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2)) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_iff_affineRemainder.mpr h

/-- A neighborhood family of quadratic norm bounds for the remainder after subtracting a proposed
quadratic part is exactly the estimate needed for the project second-order expansion predicate. -/
theorem affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [h c hc] with z hz
  have hsq_norm : ‖(‖z‖ ^ 2 : ℝ)‖ = ‖z‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  simpa [hsq_norm] using hz

/-- Local quadratic norm estimates after subtracting a proposed quadratic part give the
corresponding second-order expansion. -/
theorem hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    (affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul h)

/-- Local quadratic norm estimates after subtracting a symmetric proposed quadratic part give
second-order differentiability. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul h)

/-- A punctured-neighborhood normalized quotient bound after subtracting a proposed quadratic
part gives the little-o estimate for the project second-order expansion predicate. -/
theorem affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  apply affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul
  intro ε hε
  have hpunctured :=
    (eventually_nhdsWithin_iff.mp (h ε hε) :
      ∀ᶠ z in nhds (0 : E), z ∈ ({z : E | z ≠ 0}) →
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε)
  filter_upwards [hpunctured] with z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hquot :
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε := by
      exact hz hz0
    have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz0)
    exact (div_le_iff₀ hden).mp hquot

/-- A punctured-neighborhood normalized quotient bound after subtracting a proposed quadratic
part gives the corresponding second-order expansion. -/
theorem hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    (affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_div_norm_sq_le h)

/-- A punctured-neighborhood normalized quotient bound after subtracting a symmetric proposed
quadratic part gives second-order differentiability. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le h)

/-- Conjugate a continuous linear operator by a linear isometry equivalence.  This is the Hessian
candidate obtained when pulling quadratic estimate data back from an isometric coordinate model. -/
def linearIsometryEquivConjCLM (e : E ≃ₗᵢ[ℝ] F) (B : F →L[ℝ] F) : E →L[ℝ] E :=
  e.symm.toLinearIsometry.toContinuousLinearMap.comp
    (B.comp e.toLinearIsometry.toContinuousLinearMap)

/-- Symmetry of a Hessian candidate is preserved by isometric coordinate conjugation. -/
theorem isSymmetricOperator_linearIsometryEquivConjCLM
    (e : E ≃ₗᵢ[ℝ] F) {B : F →L[ℝ] F} (hB : IsSymmetricOperator B) :
    IsSymmetricOperator (linearIsometryEquivConjCLM e B) := by
  have hconj :
      ((e.symm.toLinearMap : F →ₗ[ℝ] E) ∘ₗ (B : F →ₗ[ℝ] F) ∘ₗ
          (e.toLinearMap : E →ₗ[ℝ] F)).IsSymmetric := by
    exact
      (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff
        (T := (B : F →ₗ[ℝ] F)) (f := e.symm)).2 hB
  change ((e.symm.toLinearIsometry.toLinearMap : F →ₗ[ℝ] E) ∘ₗ
    (B : F →ₗ[ℝ] F) ∘ₗ (e.toLinearIsometry.toLinearMap : E →ₗ[ℝ] F)).IsSymmetric
  exact hconj

/-- The quadratic form of a conjugated operator is the coordinate-model quadratic form. -/
theorem inner_linearIsometryEquivConjCLM_self
    (e : E ≃ₗᵢ[ℝ] F) (B : F →L[ℝ] F) (z : E) :
    inner ℝ z ((linearIsometryEquivConjCLM e B) z) =
      inner ℝ (e z) (B (e z)) := by
  have hinner :=
    LinearIsometryEquiv.inner_map_map e z ((linearIsometryEquivConjCLM e B) z)
  rw [← hinner]
  congr 1
  simp [linearIsometryEquivConjCLM]

end AleksandrovDifferentiability
