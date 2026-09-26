import Mathlib

noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability.AffineModelStatement

def Claim : Prop :=
  ∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p x : E) (c : ℝ),
      ∃ q : E, ∃ B : E →L[ℝ] E,
        (B : E →ₗ[ℝ] E).IsSymmetric ∧
          (fun z : E =>
              (inner ℝ p (x + z) + c) - (inner ℝ p x + c) - inner ℝ q z -
                (1 / 2 : ℝ) * inner ℝ z (B z))
            =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

end AleksandrovDifferentiability.AffineModelStatement
