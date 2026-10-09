module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.Core

/-!
# Line geometry for unit-direction slicing
-/

@[expose] public noncomputable section

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

end AleksandrovDifferentiability
