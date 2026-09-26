import Statement
import AleksandrovDifferentiability

noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability

theorem challenge_second_order_witness_interface : SecondOrderWitnessStatement.Claim := by
  unfold SecondOrderWitnessStatement.Claim
  intro E _ _ u x h
  exact h

end AleksandrovDifferentiability
