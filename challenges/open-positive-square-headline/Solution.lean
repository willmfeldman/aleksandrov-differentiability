import AleksandrovDifferentiability
import Mathlib.Analysis.Convex.Mul

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
  have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun y : ℝ => y ^ 2) :=
    (convexOn_pow (𝕜 := ℝ) 2).subset Set.Ioi_subset_Ici_self (convex_Ioi (0 : ℝ))
  exact
    (convexAleksandrovAE
      (E := ℝ) (Ω := Set.Ioi (0 : ℝ)) (u := fun y : ℝ => y ^ 2)
      isOpen_Ioi hconv).mono fun _ hx => hx

end AleksandrovDifferentiability
