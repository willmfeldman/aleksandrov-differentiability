module

public import AleksandrovDifferentiability.Analysis.GoodSet
public import AleksandrovDifferentiability.Analysis.QuadraticTrap

/-!
# Assembly from quadratic estimates

This file packages the passage from full-measure sets carrying pointwise quadratic remainder
estimates to the project almost-everywhere differentiability conclusions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- If a full-measure set in `s` carries explicit symmetric quadratic data whose affine
remainder error is locally `ε * ‖z‖ ^ 2` for every `ε > 0`, then `u` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_expansionData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hest⟩
    exact ⟨p, B, hB,
      hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest⟩)

/-- Quotient-estimate version of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_expansionData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hest⟩
    exact ⟨p, B, hB,
      hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
        hest⟩)

/-- Countable full-measure good sets whose simultaneous validity gives symmetric local
quadratic remainder estimates imply second-order differentiability almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_expansionData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hest⟩
    exact ⟨p, B, hB,
      hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul hest⟩)

/-- Quotient-estimate version of
`secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticQuotientEstimateData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_expansionData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hest⟩
    exact ⟨p, B, hB,
      hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
        hest⟩)

/-- If the named ambient quadratic estimate set has full measure in `s`, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateSet
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ quadraticEstimateSet u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact quadraticEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- If the named ambient quadratic quotient-estimate set has full measure in `s`, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateSet
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ quadraticQuotientEstimateSet u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact quadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- Full measure of the local ambient quadratic estimate set implies full measure of the
punctured normalized quotient-estimate set. -/
theorem measure_diff_quadraticQuotientEstimateSet_eq_zero_of_quadraticEstimateSet
    {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hnull : μ (s \ quadraticEstimateSet u) = 0) :
    μ (s \ quadraticQuotientEstimateSet u) = 0 := by
  refine measure_mono_null ?_ hnull
  intro x hx
  exact ⟨hx.1, fun hxq => hx.2 (quadraticEstimateSet_subset_quadraticQuotientEstimateSet hxq)⟩

/-- Real-line scalar version of the full-measure quadratic-estimate assembly lemma. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimate
    {μ : Measure ℝ} {s G : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → x ∈ G →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, hest⟩
    exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_le_mul hest)

/-- Real-line scalar quotient-estimate version of
`secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimate`. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimate
    {μ : Measure ℝ} {s G : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → x ∈ G →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, hest⟩
    exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le hest)

/-- Countable real-line scalar quadratic-estimate assembly lemma. -/
theorem secondOrderDifferentiableAEOn_real_of_countable_scalarEstimate
    {μ : Measure ℝ} {s : Set ℝ} {G : ℕ → Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, hest⟩
    exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_le_mul hest)

/-- Countable real-line scalar quotient-estimate assembly lemma. -/
theorem secondOrderDifferentiableAEOn_real_of_countable_scalarQuotientEstimate
    {μ : Measure ℝ} {s : Set ℝ} {G : ℕ → Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, hest⟩
    exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le hest)

/-- If the named real-line scalar estimate set has full measure in `s`, then `f` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticEstimateSet f) = 0) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact realScalarQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- If the named real-line scalar quotient-estimate set has full measure in `s`, then `f` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    SecondOrderDifferentiableAEOn μ s f :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact realScalarQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- Full measure of the local real-line scalar quadratic estimate set implies full measure of
the punctured normalized scalar quotient-estimate set. -/
theorem measure_diff_realScalarQuadraticQuotientEstimateSet_eq_zero_of_estimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ}
    (hnull : μ (s \ realScalarQuadraticEstimateSet f) = 0) :
    μ (s \ realScalarQuadraticQuotientEstimateSet f) = 0 := by
  refine measure_mono_null ?_ hnull
  intro x hx
  exact
    ⟨hx.1, fun hxq =>
      hx.2 (realScalarQuadraticEstimateSet_subset_realScalarQuadraticQuotientEstimateSet hxq)⟩

/-- Null-bad-set form of the real-line scalar full-measure estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimate
    {μ : Measure ℝ} {s G : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → x ∈ G →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimate hs hnull hG)

/-- Null-bad-set form of the real-line scalar quotient-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarQuotientEstimate
    {μ : Measure ℝ} {s G : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → x ∈ G →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimate hs hnull hG)

/-- Null-bad-set form of the countable real-line scalar estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_countable_scalarEstimate
    {μ : Measure ℝ} {s : Set ℝ} {G : ℕ → Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_countable_scalarEstimate hs hnull hG)

/-- Null-bad-set form of the countable real-line scalar quotient-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_countable_scalarQuotientEstimate
    {μ : Measure ℝ} {s : Set ℝ} {G : ℕ → Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : ℝ⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : ℝ, ∃ q : ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
            ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_countable_scalarQuotientEstimate hs hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticEstimateSet f) = 0) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimateSet hs hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarQuotientEstimateSet
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    μ (secondOrderBadSetOn s f) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimateSet hs hnull)

/-- Null-bad-set form of the local quadratic-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticEstimateData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData hs hnull hG)

/-- Null-bad-set form of the quotient-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticQuotientEstimateData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateData hs hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticEstimateSet
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ quadraticEstimateSet u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateSet hs hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticQuotientEstimateSet
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ quadraticQuotientEstimateSet u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateSet hs hnull)

/-- Null-bad-set form of the countable local quadratic-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_quadraticEstimateData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData hs hnull hG)

/-- Null-bad-set form of the countable quotient-estimate assembly lemma. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_quadraticQuotientEstimateData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticQuotientEstimateData
      hs hnull hG)

end AleksandrovDifferentiability
