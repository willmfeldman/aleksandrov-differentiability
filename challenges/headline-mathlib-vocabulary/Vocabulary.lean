module

public import Mathlib

@[expose] public section

noncomputable section

open Asymptotics MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability.HeadlineMathlibVocabularyStatement

def Claim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}, IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        ∃ p : E, ∃ B : E →L[ℝ] E,
          (∀ z w : E, inner ℝ (B z) w = inner ℝ z (B w)) ∧
            (fun z : E =>
                u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
              =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

end AleksandrovDifferentiability.HeadlineMathlibVocabularyStatement

end
