import Statement
import AleksandrovDifferentiability

noncomputable section

namespace AleksandrovDifferentiability

theorem challenge_affine_model_case : AffineModelStatement.Claim := by
  unfold AffineModelStatement.Claim
  intro E _ _ p x c
  exact secondOrderDifferentiableAt_inner_add_const p c x

end AleksandrovDifferentiability
