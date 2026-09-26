module

public import AleksandrovDifferentiability.Analysis.Directional.Assembly

/-!
# Countable directional null-set assembly

This file upgrades countable families of full-measure directional estimate sets to the
almost-everywhere second-order differentiability statements used by the final assembly layer.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Countable full-measure assembly from estimates whose quadratic model is a finite
mixed-directional coefficient matrix. -/
theorem secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticEstimateData
    {ι : Type*} {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ a : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
              ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, a, hest⟩
    exact ⟨p, mixedDirectionalQuadraticSum D v a,
      isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticEstimateData`. -/
theorem secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticQuotientData
    {ι : Type*} {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ a : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticQuotientEstimateData hs hnull
    (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, a, hest⟩
      exact ⟨p, mixedDirectionalQuadraticSum D v a,
        isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩)

/-- Countable full-measure assembly from polarized pure and pairwise-sum directional
coefficient data. -/
theorem secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticEstimateData
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
              ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, r, hest⟩
    exact ⟨p, polarizedMixedQuadraticSum D v q r,
      isSymmetricOperator_polarizedMixedQuadraticSum D v q r, hest⟩)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticEstimateData`. -/
theorem
    secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticQuotientData
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticQuotientEstimateData hs hnull
    (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, q, r, hest⟩
      exact ⟨p, polarizedMixedQuadraticSum D v q r,
        isSymmetricOperator_polarizedMixedQuadraticSum D v q r, hest⟩)

/-- Countable full-measure assembly from arbitrary symmetric ambient quadratic estimate data
whose pure and off-diagonal pairwise-sum coefficients match a finite orthonormal spanning frame. -/
theorem secondOrderDifferentiableAEOn_of_countable_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticEstimateData
    hs D v hnull (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, B, q, r, hB, hest, hr, hpure, hpair⟩
      exact polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
        hv hB hest hr hpure hpair)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_countable_quadraticEstimateData_coefficients`. -/
theorem secondOrderDifferentiableAEOn_of_countable_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticQuotientData
    hs D v hnull (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, B, q, r, hB, hest, hr, hpure, hpair⟩
      exact
        polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
          hv hB hest hr hpure hpair)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData_coefficients`. -/
theorem measure_badSetOn_eq_zero_of_fullMeasure_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData_coefficients
      hs D v hv hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientData_coefficients`. -/
theorem measure_badSetOn_eq_zero_of_fullMeasure_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientData_coefficients
      hs D v hv hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_countable_quadraticEstimateData_coefficients`. -/
theorem measure_badSetOn_eq_zero_of_countable_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_quadraticEstimateData_coefficients
      hs D v hv hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_countable_quadraticQuotientData_coefficients`. -/
theorem measure_badSetOn_eq_zero_of_countable_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {G : ℕ → Set E}
    {u : E → ℝ} (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_quadraticQuotientData_coefficients
      hs D v hv hnull hG)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
      hs D v hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
      hs D v hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticSet`. -/
theorem measure_badSetOn_eq_zero_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
      hs D v hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuotientSet`. -/
theorem measure_badSetOn_eq_zero_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuotientSet
      hs D v hnull)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction`. -/
theorem measure_badSetOn_eq_zero_of_fullMeasure_directionalSliceSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction
      hs D v hnull hrecon)

/-- Null-bad-set form of
`secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction`. -/
theorem
    measure_badSetOn_eq_zero_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
      hs D v hnull hrecon)

/-- Null-bad-set form of polarized reconstruction from the finite slice-estimate set. -/
theorem measure_badSetOn_eq_zero_of_directionalSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
      hs D v hnull hrecon)

/-- Null-bad-set form of polarized reconstruction from the finite slice quotient-estimate set. -/
theorem measure_badSetOn_eq_zero_of_directionalSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
      hs D v hnull hrecon)


end AleksandrovDifferentiability
