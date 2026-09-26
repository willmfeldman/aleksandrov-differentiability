import Mathlib

noncomputable section

open Asymptotics MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability.BoundedAbsHeadlineStatement

def SecondOrderDifferentiableAt (u : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ p : ℝ, ∃ B : ℝ →L[ℝ] ℝ,
    (B : ℝ →ₗ[ℝ] ℝ).IsSymmetric ∧
      (fun z : ℝ =>
          u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
        =o[𝓝 0] (fun z : ℝ => ‖z‖ ^ 2)

def Claim : Prop :=
  (∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
      SecondOrderDifferentiableAt (fun y : ℝ => |y|) x) ∧
    ¬ SecondOrderDifferentiableAt (fun y : ℝ => |y|) 0 ∧
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
      SecondOrderDifferentiableAt (fun y : ℝ => |y|) x

end AleksandrovDifferentiability.BoundedAbsHeadlineStatement
