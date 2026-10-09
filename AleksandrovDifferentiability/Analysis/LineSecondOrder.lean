module

public import AleksandrovDifferentiability.Analysis.QuadraticTrap
public import AleksandrovDifferentiability.Foundation.SecondOrder

/-!
# Second order expansions on affine lines

This file connects the ambient second-order expansion predicate to one-dimensional restrictions
along affine lines.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the real line, every scalar multiple of the identity is a symmetric operator. -/
theorem isSymmetricOperator_real_smul_one (c : ℝ) :
    IsSymmetricOperator (c • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [IsSymmetricOperator]
  exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one

end AleksandrovDifferentiability
