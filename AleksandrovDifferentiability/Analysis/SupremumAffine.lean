module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Suprema of affine functions

This file records a small convexity fact used by the public comparator: a pointwise supremum of
affine functions is convex when the real supremum is pointwise bounded above.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

/-- The pointwise supremum of a nonempty pointwise bounded-above family of affine functions
`x ↦ ⟪p i, x⟫ + b i` is convex. -/
theorem convexOn_univ_iSup_inner_add
    {ι E : Type*} [Nonempty ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ι → E) (b : ι → ℝ)
    (hBdd : ∀ x : E, BddAbove (Set.range fun i : ι => inner ℝ (p i) x + b i)) :
    ConvexOn ℝ (Set.univ : Set E)
      (fun x : E => ⨆ i : ι, inner ℝ (p i) x + b i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hac
  suffices
      (⨆ i : ι, inner ℝ (p i) (a • x + c • y) + b i) ≤
        a * (⨆ i : ι, inner ℝ (p i) x + b i) +
          c * (⨆ i : ι, inner ℝ (p i) y + b i) by
    simpa [smul_eq_mul] using this
  refine ciSup_le fun i => ?_
  calc
    inner ℝ (p i) (a • x + c • y) + b i
        = a * (inner ℝ (p i) x + b i) + c * (inner ℝ (p i) y + b i) := by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
          have hb : b i = a * b i + c * b i := by
            calc
              b i = (a + c) * b i := by rw [hac, one_mul]
              _ = a * b i + c * b i := by ring
          conv_lhs => rw [hb]
          ring
    _ ≤ a * (⨆ j : ι, inner ℝ (p j) x + b j) +
          c * (⨆ j : ι, inner ℝ (p j) y + b j) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_ciSup (hBdd x) i) ha)
          (mul_le_mul_of_nonneg_left (le_ciSup (hBdd y) i) hc)

end AleksandrovDifferentiability
