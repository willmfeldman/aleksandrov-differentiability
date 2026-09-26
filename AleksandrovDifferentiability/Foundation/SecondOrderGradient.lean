module

public import AleksandrovDifferentiability.Foundation.SecondOrder
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# First-order consequence of the second-order expansion

This file bridges the project second-order expansion predicate to Mathlib's Fréchet derivative:
a second-order expansion at `x` with first-order vector `p` yields `HasFDerivAt u (innerSL ℝ p) x`.
-/

@[expose] public noncomputable section

open Asymptotics
open scoped Topology

namespace AleksandrovDifferentiability

/-- A second-order expansion at `x` yields the first derivative: the first-order vector `p`
represents the Fréchet derivative of `u` at `x` through the inner product. -/
theorem HasSecondOrderExpansionAt.hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) :
    HasFDerivAt u (innerSL ℝ p) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hsq : (fun z : E => ‖z‖ ^ 2) =o[𝓝 (0 : E)] fun z : E => z :=
    isLittleO_norm_pow_id one_lt_two
  have hrem :
      (fun z : E =>
          u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
        =o[𝓝 (0 : E)] fun z : E => z :=
    h.trans hsq
  have hquadO :
      (fun z : E => (1 / 2 : ℝ) * inner ℝ z (B z)) =O[𝓝 (0 : E)]
        fun z : E => ‖z‖ ^ 2 := by
    refine IsBigO.of_bound ((1 / 2 : ℝ) * ‖B‖) ?_
    filter_upwards with z
    have hCS : ‖inner ℝ z (B z)‖ ≤ ‖z‖ * ‖B z‖ := norm_inner_le_norm (𝕜 := ℝ) z (B z)
    have hop : ‖z‖ * ‖B z‖ ≤ ‖z‖ * (‖B‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm z) (norm_nonneg z)
    have hhalf : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by
      rw [Real.norm_eq_abs]
      norm_num
    calc
      ‖(1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤ (1 / 2 : ℝ) * (‖z‖ * (‖B‖ * ‖z‖)) := by
        rw [norm_mul, hhalf]
        exact mul_le_mul_of_nonneg_left (hCS.trans hop) (by norm_num)
      _ = (1 / 2 : ℝ) * ‖B‖ * ‖(‖z‖ ^ 2)‖ := by
        rw [Real.norm_of_nonneg (by positivity)]
        ring
  have hquad :
      (fun z : E => (1 / 2 : ℝ) * inner ℝ z (B z)) =o[𝓝 (0 : E)] fun z : E => z :=
    hquadO.trans_isLittleO hsq
  refine (hrem.add hquad).congr_left fun z => ?_
  rw [innerSL_apply_apply]
  ring

end AleksandrovDifferentiability
