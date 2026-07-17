import AleksandrovDifferentiability

noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

theorem challenge_headline_in_mathlib_vocabulary
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure E).restrict Ω),
      ∃ p : E, ∃ B : E →L[ℝ] E,
        (∀ z w : E, inner ℝ (B z) w = inner ℝ z (B w)) ∧
          (fun z : E =>
              u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
            =o[𝓝 0] (fun z : E => ‖z‖ ^ 2) := by
  exact (convexAleksandrovAE (E := E) (Ω := Ω) (u := u) hΩ hu).mono fun _ hx => hx

end AleksandrovDifferentiability
