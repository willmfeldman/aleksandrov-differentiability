import AleksandrovDifferentiability

noncomputable section

namespace AleksandrovDifferentiability

theorem challenge_affine_model_case
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p x : E) (c : ℝ) :
    SecondOrderDifferentiableAt (fun y : E => inner ℝ p y + c) x :=
  secondOrderDifferentiableAt_inner_add_const p c x

end AleksandrovDifferentiability
