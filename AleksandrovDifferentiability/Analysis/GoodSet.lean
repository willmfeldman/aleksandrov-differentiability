module

public import AleksandrovDifferentiability.Foundation.SecondOrder
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Good and bad sets for second-order differentiability

This file gives names to the full-measure and exceptional-set formulations of the final
second-order differentiability conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exceptional set where `u` is not second-order differentiable. -/
def secondOrderBadSet (u : E → ℝ) : Set E :=
  (secondOrderDifferentiabilitySet u)ᶜ

/-- The exceptional set inside a prescribed domain. -/
def secondOrderBadSetOn (s : Set E) (u : E → ℝ) : Set E :=
  s \ secondOrderDifferentiabilitySet u

@[simp]
theorem mem_secondOrderBadSet {u : E → ℝ} {x : E} :
    x ∈ secondOrderBadSet u ↔ ¬ SecondOrderDifferentiableAt u x := by
  rfl

@[simp]
theorem mem_secondOrderBadSetOn {s : Set E} {u : E → ℝ} {x : E} :
    x ∈ secondOrderBadSetOn s u ↔ x ∈ s ∧ ¬ SecondOrderDifferentiableAt u x := by
  rfl

variable [MeasurableSpace E]

/-- `u` is second-order differentiable almost everywhere with respect to `μ`. -/
def SecondOrderDifferentiableAE (μ : Measure E) (u : E → ℝ) : Prop :=
  ∀ᵐ x ∂μ, SecondOrderDifferentiableAt u x

/-- `u` is second-order differentiable almost everywhere on `s`, with respect to `μ`. -/
def SecondOrderDifferentiableAEOn (μ : Measure E) (s : Set E) (u : E → ℝ) : Prop :=
  ∀ᵐ x ∂(μ.restrict s), SecondOrderDifferentiableAt u x

theorem secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {u : E → ℝ} :
    SecondOrderDifferentiableAE μ u ↔ μ (secondOrderBadSet u) = 0 := by
  rw [SecondOrderDifferentiableAE, ae_iff]
  have hset : {x | ¬ SecondOrderDifferentiableAt u x} = secondOrderBadSet u := by
    ext x
    rfl
  rw [hset]

theorem secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} :
    SecondOrderDifferentiableAEOn μ s u ↔ μ.restrict s (secondOrderBadSet u) = 0 := by
  rw [SecondOrderDifferentiableAEOn]
  exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero

/-- Restricted-measure null-bad-set form of an a.e.-on statement. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    {μ : Measure E} {s : Set E} {u : E → ℝ}
    (h : SecondOrderDifferentiableAEOn μ s u) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero.mp h

omit [MeasurableSpace E] in
theorem secondOrderBadSet_inter_eq_secondOrderBadSetOn
    {s : Set E} {u : E → ℝ} :
    secondOrderBadSet u ∩ s = secondOrderBadSetOn s u := by
  ext x
  simp [and_comm]

theorem secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s) :
    SecondOrderDifferentiableAEOn μ s u ↔ μ (secondOrderBadSetOn s u) = 0 := by
  rw [secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero]
  rw [Measure.restrict_apply_eq_zero' hs]
  rw [secondOrderBadSet_inter_eq_secondOrderBadSetOn]

theorem secondOrderDifferentiableAEOn_of_secondOrderBadSetOn_subset_null
    {μ : Measure E} {s : Set E} {u : E → ℝ} {N : Set E} (hs : MeasurableSet s)
    (hsubset : secondOrderBadSetOn s u ⊆ N) (hN : μ N = 0) :
    SecondOrderDifferentiableAEOn μ s u := by
  rw [secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs]
  exact le_antisymm ((measure_mono hsubset).trans_eq hN) bot_le

omit [MeasurableSpace E] in
theorem secondOrderBadSetOn_subset_domain_diff_of_inter_subset_differentiabilitySet
    {s G : Set E} {u : E → ℝ}
    (hG : s ∩ G ⊆ secondOrderDifferentiabilitySet u) :
    secondOrderBadSetOn s u ⊆ s \ G := by
  intro x hx
  rcases (mem_secondOrderBadSetOn.mp hx) with ⟨hxs, hxbad⟩
  refine ⟨hxs, ?_⟩
  intro hxG
  exact hxbad (by simpa using hG ⟨hxs, hxG⟩)

theorem secondOrderDifferentiableAEOn_of_fullMeasure_goodSet
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : s ∩ G ⊆ secondOrderDifferentiabilitySet u) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_secondOrderBadSetOn_subset_null hs
    (secondOrderBadSetOn_subset_domain_diff_of_inter_subset_differentiabilitySet hG) hnull

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- If `G` has full measure inside `s`, then almost every point of `s`, for the restricted
measure, belongs to `G`. This version does not require measurability of `G`. -/
theorem ae_restrict_mem_of_measure_diff_eq_zero
    {μ : Measure E} {s G : Set E} (hs : MeasurableSet s) (hnull : μ (s \ G) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ G := by
  rw [ae_iff]
  rw [Measure.restrict_apply_eq_zero' hs]
  have hset : {x : E | ¬x ∈ G} ∩ s = s \ G := by
    ext x
    simp [and_comm]
  rwa [hset]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A.e. membership in `G` for the restricted measure is the same as `G` having null complement
inside `s`.  This version does not require measurability of `G`. -/
theorem measure_diff_eq_zero_of_ae_restrict_mem
    {μ : Measure E} {s G : Set E} (hs : MeasurableSet s)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ G) :
    μ (s \ G) = 0 := by
  rw [ae_iff] at hmem
  rw [Measure.restrict_apply_eq_zero' hs] at hmem
  have hset : {x : E | ¬x ∈ G} ∩ s = s \ G := by
    ext x
    simp [and_comm]
  rwa [hset] at hmem

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Full-measure-in-`s` is monotone when the good set is enlarged. -/
theorem measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    {μ : Measure E} {s G H : Set E} (hGH : G ⊆ H) (hG : μ (s \ G) = 0) :
    μ (s \ H) = 0 := by
  have hsubset : s \ H ⊆ s \ G := by
    intro x hx
    exact ⟨hx.1, fun hxG => hx.2 (hGH hxG)⟩
  exact le_antisymm ((measure_mono hsubset).trans_eq hG) bot_le

section HilbertCLM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H]

end HilbertCLM

end AleksandrovDifferentiability
