import Mathlib

noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability

def IsSymmetricOperator {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) : Prop :=
  (B : E →ₗ[ℝ] E).IsSymmetric

def HasSecondOrderExpansionAt
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (x p : E) (B : E →L[ℝ] E) : Prop :=
  (fun z : E =>
      u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
    =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

def SecondOrderDifferentiableAt
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ B : E →L[ℝ] E,
    IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B

theorem challenge_second_order_witness_interface
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {x : E} (h : SecondOrderDifferentiableAt u x) :
    ∃ p : E, ∃ B : E →L[ℝ] E,
      IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B := by
  sorry

end AleksandrovDifferentiability
