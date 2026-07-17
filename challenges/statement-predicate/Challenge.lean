import Mathlib

noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

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

def ConvexAleksandrovAEStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ᵐ x ∂(volume.restrict Ω), SecondOrderDifferentiableAt u x

theorem challenge_statement_predicate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u := by
  sorry

end AleksandrovDifferentiability
