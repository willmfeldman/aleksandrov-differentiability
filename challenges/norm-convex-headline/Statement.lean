import Mathlib

noncomputable section

open Asymptotics MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability.NormConvexHeadlineStatement

def Claim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E],
      ∀ᵐ x ∂((volume : Measure E).restrict (Set.univ : Set E)),
        ∃ p : E, ∃ B : E →L[ℝ] E,
          (∀ z w : E, inner ℝ (B z) w = inner ℝ z (B w)) ∧
            (fun z : E =>
                ‖x + z‖ - ‖x‖ - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
              =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

end AleksandrovDifferentiability.NormConvexHeadlineStatement
