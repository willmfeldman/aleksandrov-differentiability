module

public import AleksandrovDifferentiability.Analysis.Directional.CountableNull
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Frame
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Operators
public import AleksandrovDifferentiability.Analysis.EstimateAssembly
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar
public import AleksandrovDifferentiability.Foundation.SecondOrder
public import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
public import AleksandrovDifferentiability.Statements.Aleksandrov.Core

/-!
# Countable and real-line reductions to the a.e. theorem
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives local quadratic remainder estimates. -/
theorem convexAleksandrovAEStatement_of_countable_fullMeasure_quadraticEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                    ε * ‖z‖ ^ 2) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives punctured normalized quadratic remainder estimates. -/
theorem convexAleksandrovAEStatement_of_countable_fullMeasure_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_fullMeasure_quadraticQuotientEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives local estimates with a finite directional-coefficient Hessian candidate. -/
theorem convexAleksandrovAEStatement_of_countable_mixedDirectionalQuadraticEstimateData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticEstimateData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives punctured normalized estimates with a finite directional-coefficient Hessian
candidate. -/
theorem convexAleksandrovAEStatement_of_countable_mixedDirectionalQuadraticQuotientData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticQuotientData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives local estimates with a polarized directional-coefficient Hessian candidate. -/
theorem convexAleksandrovAEStatement_of_countable_polarizedMixedDirectionalQuadraticEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticEstimateData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from countably many full-measure good sets whose simultaneous
membership gives punctured normalized estimates with a polarized directional-coefficient Hessian
candidate. -/
theorem convexAleksandrovAEStatement_of_countable_polarizedMixedDirectionalQuadraticQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact
    secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG

/-- Countable final-assembly reduction from arbitrary symmetric ambient Hessian candidates with
prescribed finite-frame pure and off-diagonal pairwise-sum coefficients. -/
theorem convexAleksandrovAEStatement_of_countable_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            IsSymmetricOperator B ∧
              (∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) -
                      (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤ ε * ‖z‖ ^ 2) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
              (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
                inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_quadraticEstimateData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Punctured normalized quotient version of
`convexAleksandrovAEStatement_of_countable_quadraticEstimateData_coefficients`. -/
theorem convexAleksandrovAEStatement_of_countable_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            IsSymmetricOperator B ∧
              (∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) -
                      (1 / 2 : ℝ) * inner ℝ z (B z)‖ / ‖z‖ ^ 2 ≤ ε) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
              (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
                inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_quadraticQuotientData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Real-line theorem-boundary reduction from scalar local quadratic estimates. -/
theorem convexAleksandrovAEStatement_real_of_fullMeasure_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Real-line theorem-boundary reduction from scalar punctured normalized quadratic estimates. -/
theorem convexAleksandrovAEStatement_real_of_fullMeasure_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_real_of_fullMeasure_scalarQuotientEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Real-line theorem-boundary reduction from countably many scalar estimate good sets. -/
theorem convexAleksandrovAEStatement_real_of_countable_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_real_of_countable_scalarEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Real-line theorem-boundary reduction from countably many scalar quotient-estimate good sets. -/
theorem convexAleksandrovAEStatement_real_of_countable_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovAEStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_real_of_countable_scalarQuotientEstimate
    (μ := volume) hΩ.measurableSet hnull hG

end AleksandrovDifferentiability
