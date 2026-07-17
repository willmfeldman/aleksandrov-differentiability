import AleksandrovDifferentiability

noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability

theorem challenge_second_order_witness_interface
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {x : E} (h : SecondOrderDifferentiableAt u x) :
    ∃ p : E, ∃ B : E →L[ℝ] E,
      IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B :=
  h

end AleksandrovDifferentiability
