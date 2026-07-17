import AleksandrovDifferentiability.Analysis.LineAleksandrov.Core

/-!
# Line geometry for unit-direction slicing
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The span of a unit vector is linearly isometric to `ℝ` by taking the scalar coordinate. -/
def unitSpanLinearIsometryEquivReal (ξ : E) (hξ : ‖ξ‖ = 1) : (ℝ ∙ ξ) ≃ₗᵢ[ℝ] ℝ := by
  have hξne : ξ ≠ 0 := by
    intro hzero
    simp [hzero] at hξ
  refine (LinearEquiv.coord ℝ E ξ hξne).isometryOfInner ?_
  intro x y
  have hx : (LinearEquiv.coord ℝ E ξ hξne x) • ξ = (x : E) :=
    LinearEquiv.coord_apply_smul ℝ E ξ hξne x
  have hy : (LinearEquiv.coord ℝ E ξ hξne y) • ξ = (y : E) :=
    LinearEquiv.coord_apply_smul ℝ E ξ hξne y
  change inner ℝ ((LinearEquiv.coord ℝ E ξ hξne) x)
      ((LinearEquiv.coord ℝ E ξ hξne) y) = inner ℝ (x : E) (y : E)
  have hrhs : inner ℝ (x : E) (y : E) =
      (LinearEquiv.coord ℝ E ξ hξne y) * (LinearEquiv.coord ℝ E ξ hξne x) := by
    rw [← hx, ← hy]
    rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, hξ]
    simp [mul_comm]
  simpa [RCLike.inner_apply, mul_comm] using hrhs.symm

@[simp]
theorem unitSpanLinearIsometryEquivReal_apply_self (ξ : E) (hξ : ‖ξ‖ = 1) :
    unitSpanLinearIsometryEquivReal ξ hξ
      (⟨ξ, Submodule.mem_span_singleton_self ξ⟩ : ℝ ∙ ξ) = 1 := by
  unfold unitSpanLinearIsometryEquivReal
  simp [LinearEquiv.coord_self]

/-- Splitting by the hyperplane perpendicular to `ξ` sends `ξ` to its vertical component. -/
theorem orthogonalDecomposition_orthogonal_span_singleton_apply_self (ξ : E) :
    ((ℝ ∙ ξ)ᗮ).orthogonalDecomposition ξ =
      WithLp.toLp 2
        ((0 : (ℝ ∙ ξ)ᗮ),
          (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
            ((ℝ ∙ ξ)ᗮ)ᗮ)) := by
  rw [Submodule.orthogonalDecomposition_apply]
  congr
  · exact Submodule.orthogonalProjection_orthogonal_apply_eq_zero
      (K := ℝ ∙ ξ) (Submodule.mem_span_singleton_self ξ)
  · exact Submodule.orthogonalProjection_mem_subspace_eq_self
      (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
        ((ℝ ∙ ξ)ᗮ)ᗮ)

/-- A canonical coordinate model sending a unit direction to the vertical vector `(0,1)`.

The first factor is the hyperplane perpendicular to the direction, and the second factor is the
scalar coordinate on the line spanned by the direction. -/
def verticalizingLinearIsometryEquiv (ξ : E) (hξ : ‖ξ‖ = 1) :
    E ≃ₗᵢ[ℝ] WithLp 2 (((ℝ ∙ ξ)ᗮ) × ℝ) :=
  let K : Submodule ℝ E := (ℝ ∙ ξ)ᗮ
  let horth : Kᗮ = ℝ ∙ ξ := Submodule.orthogonal_orthogonal (ℝ ∙ ξ)
  let lineToReal : Kᗮ ≃ₗᵢ[ℝ] ℝ :=
    (LinearIsometryEquiv.ofEq Kᗮ (ℝ ∙ ξ) horth).trans
      (unitSpanLinearIsometryEquivReal ξ hξ)
  K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ K) lineToReal)

@[simp]
theorem verticalizingLinearIsometryEquiv_apply_self (ξ : E) (hξ : ‖ξ‖ = 1) :
    verticalizingLinearIsometryEquiv ξ hξ ξ =
      WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ) := by
  dsimp [verticalizingLinearIsometryEquiv]
  let K : Submodule ℝ E := (ℝ ∙ ξ)ᗮ
  let horth : Kᗮ = ℝ ∙ ξ := Submodule.orthogonal_orthogonal (ℝ ∙ ξ)
  have hfst : (((ℝ ∙ ξ)ᗮ).orthogonalDecomposition ξ).fst = (0 : (ℝ ∙ ξ)ᗮ) := by
    rw [Submodule.fst_orthogonalDecomposition_apply]
    exact Submodule.orthogonalProjection_orthogonal_apply_eq_zero
      (K := ℝ ∙ ξ) (Submodule.mem_span_singleton_self ξ)
  have hsnd :
      (((ℝ ∙ ξ)ᗮ).orthogonalDecomposition ξ).snd =
        (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
          ((ℝ ∙ ξ)ᗮ)ᗮ) := by
    rw [Submodule.snd_orthogonalDecomposition_apply]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self
      (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
        ((ℝ ∙ ξ)ᗮ)ᗮ)
  have hofEq :
      (LinearIsometryEquiv.ofEq ((ℝ ∙ ξ)ᗮ)ᗮ (ℝ ∙ ξ)
          (Submodule.orthogonal_orthogonal (ℝ ∙ ξ)))
        (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
          ((ℝ ∙ ξ)ᗮ)ᗮ) =
        (⟨ξ, Submodule.mem_span_singleton_self ξ⟩ : ℝ ∙ ξ) := by
    ext
    exact LinearIsometryEquiv.coe_ofEq_apply (Submodule.orthogonal_orthogonal (ℝ ∙ ξ))
      (⟨ξ, (ℝ ∙ ξ).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self ξ)⟩ :
        ((ℝ ∙ ξ)ᗮ)ᗮ)
  rw [hfst, hsnd, hofEq]
  simp [unitSpanLinearIsometryEquivReal_apply_self]


end AleksandrovDifferentiability
