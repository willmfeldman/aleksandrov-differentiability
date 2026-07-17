import Mathlib

noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

theorem challenge_open_positive_square_headline :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
      ∃ p : ℝ, ∃ B : ℝ →L[ℝ] ℝ,
        (∀ z w : ℝ, inner ℝ (B z) w = inner ℝ z (B w)) ∧
          (fun z : ℝ =>
              (x + z) ^ 2 - x ^ 2 - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
            =o[𝓝 0] (fun z : ℝ => ‖z‖ ^ 2) := by
  sorry

end AleksandrovDifferentiability
