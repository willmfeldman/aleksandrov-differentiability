import Mathlib

noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability.SecondOrderWitnessStatement

def Claim : Prop :=
  ∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {x : E},
      (∃ p : E, ∃ B : E →L[ℝ] E,
        (B : E →ₗ[ℝ] E).IsSymmetric ∧
          (fun z : E =>
              u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
            =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)) →
        ∃ p : E, ∃ B : E →L[ℝ] E,
          (B : E →ₗ[ℝ] E).IsSymmetric ∧
            (fun z : E =>
                u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
              =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

end AleksandrovDifferentiability.SecondOrderWitnessStatement
