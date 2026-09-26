module

public import AleksandrovDifferentiability.Statements.Aleksandrov.Reconstruction

/-!
# Equivalent Aleksandrov statement forms
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem convexAleksandrovAEStatement_iff_nullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u ↔
      ConvexAleksandrovNullBadSetStatement E Ω u := by
  unfold ConvexAleksandrovAEStatement ConvexAleksandrovNullBadSetStatement
  constructor
  · intro h hΩ hu
    exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero.mp (h hΩ hu)
  · intro h hΩ hu
    exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero.mpr (h hΩ hu)

/-- Convert the a.e. formulation into the restricted-measure null-exceptional-set formulation. -/
theorem ConvexAleksandrovAEStatement.nullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovAEStatement E Ω u) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetStatement E Ω u).mp h

/-- Convert the restricted-measure null-exceptional-set formulation into the a.e. formulation. -/
theorem ConvexAleksandrovNullBadSetStatement.aeStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovNullBadSetStatement E Ω u) :
    ConvexAleksandrovAEStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetStatement E Ω u).mpr h

theorem convexAleksandrovAEStatement_iff_nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u ↔
      ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  unfold ConvexAleksandrovAEStatement ConvexAleksandrovNullBadSetOnStatement
  constructor
  · intro h hΩ hu
    exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
      (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp (h hΩ hu)
  · intro h hΩ hu
    exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
      (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mpr (h hΩ hu)

/-- Convert the a.e. formulation into the domain-intersected null-exceptional-set formulation. -/
theorem ConvexAleksandrovAEStatement.nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovAEStatement E Ω u) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp h

/-- Convert the domain-intersected null-exceptional-set formulation into the a.e. formulation. -/
theorem ConvexAleksandrovNullBadSetOnStatement.aeStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovNullBadSetOnStatement E Ω u) :
    ConvexAleksandrovAEStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mpr h

/-- The restricted-measure and domain-intersected null-exceptional-set formulations are
equivalent for open domains. -/
theorem convexAleksandrovNullBadSetStatement_iff_nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω u ↔
      ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  rw [← convexAleksandrovAEStatement_iff_nullBadSetStatement E Ω u]
  exact convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u

/-- Convert the restricted-measure null-exceptional-set formulation into the
domain-intersected formulation. -/
theorem ConvexAleksandrovNullBadSetStatement.nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovNullBadSetStatement E Ω u) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovNullBadSetStatement_iff_nullBadSetOnStatement E Ω u).mp h

/-- Convert the domain-intersected null-exceptional-set formulation into the
restricted-measure formulation. -/
theorem ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovNullBadSetOnStatement E Ω u) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  (convexAleksandrovNullBadSetStatement_iff_nullBadSetOnStatement E Ω u).mpr h

/-- If the domain has zero Lebesgue measure, the target a.e. statement is immediate. -/
theorem convexAleksandrovAEStatement_of_volume_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (hΩ0 : volume Ω = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ _hu
  exact secondOrderDifferentiableAEOn_of_measure_eq_zero hΩ.measurableSet hΩ0

/-- Null-bad-set formulation of `convexAleksandrovAEStatement_of_volume_eq_zero`. -/
theorem convexAleksandrovNullBadSetStatement_of_volume_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (hΩ0 : volume Ω = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_volume_eq_zero E Ω u hΩ0)

/-- Domain-intersected null-bad-set formulation of
`convexAleksandrovAEStatement_of_volume_eq_zero`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_volume_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (hΩ0 : volume Ω = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro _hΩ _hu
  exact measure_secondOrderBadSetOn_eq_zero_of_measure_eq_zero hΩ0

/-- Empty-domain endpoint for the target a.e. statement. -/
theorem convexAleksandrovAEStatement_empty
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u : E → ℝ) :
    ConvexAleksandrovAEStatement E (∅ : Set E) u :=
  convexAleksandrovAEStatement_of_volume_eq_zero E (∅ : Set E) u (by simp)

/-- Empty-domain endpoint for the restricted-measure null-bad-set statement. -/
theorem convexAleksandrovNullBadSetStatement_empty
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u : E → ℝ) :
    ConvexAleksandrovNullBadSetStatement E (∅ : Set E) u :=
  convexAleksandrovNullBadSetStatement_of_volume_eq_zero E (∅ : Set E) u (by simp)

/-- Empty-domain endpoint for the domain-intersected null-bad-set statement. -/
theorem convexAleksandrovNullBadSetOnStatement_empty
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u : E → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement E (∅ : Set E) u :=
  convexAleksandrovNullBadSetOnStatement_of_volume_eq_zero E (∅ : Set E) u (by simp)

/-- Final-assembly reduction for the target statement: it is enough to produce, for every open
convex domain/function pair, a full-measure subset of the domain on which explicit symmetric
second-order expansion data exists. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_expansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_expansionData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_expansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from full-measure explicit symmetric expansion data whose
first-order term is a continuous linear functional. This is close to the form produced by
Mathlib's Fréchet derivative APIs. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from countably many full-measure good sets that jointly provide
explicit symmetric expansion data whose first-order term is a continuous linear functional. -/
theorem convexAleksandrovAEStatement_of_countable_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from full measure of a fixed CLM expansion locus. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_clmExpansionSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ volume (Ω \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨ℓ, B, hB, hnull⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet
    (μ := volume) hΩ.measurableSet hB hnull

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionSet`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_clmExpansionSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ volume (Ω \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨ℓ, B, hB, hnull⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionSet
    (μ := volume) hΩ.measurableSet hB hnull

/-- Final-assembly reduction from full measure of the named CLM expansion-data locus. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_clmExpansionDataSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ secondOrderCLMExpansionDataSet u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionDataSet`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_clmExpansionDataSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ secondOrderCLMExpansionDataSet u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionDataSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Final-assembly reduction from pointwise explicit symmetric expansion data on the whole
domain. -/
theorem convexAleksandrovAEStatement_of_forall_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ p : E, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_forall_expansionData
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_forall_expansionData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_forall_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ p : E, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_forall_expansionData
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Final-assembly reduction from pointwise explicit symmetric expansion data whose first-order
term is a continuous linear functional. This is close to the form produced by Mathlib's Fréchet
derivative APIs. -/
theorem convexAleksandrovAEStatement_of_forall_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_forall_mem
    (μ := volume) hΩ.measurableSet (by
      intro x hx
      rcases hgood hΩ hu hx with ⟨ℓ, B, hB, hquad⟩
      exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_forall_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_forall_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_forall_mem
    (μ := volume) hΩ.measurableSet (by
      intro x hx
      rcases hgood hΩ hu hx with ⟨ℓ, B, hB, hquad⟩
      exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_expansionData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_expansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_countable_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact restrict_measure_secondOrderBadSet_eq_zero_of_countable_fullMeasure_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionSet`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_clmExpansionSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ volume (Ω \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨ℓ, B, hB, hnull⟩
  exact restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionSet
    (μ := volume) hΩ.measurableSet hB hnull

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_clmExpansionDataSet`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_clmExpansionDataSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ secondOrderCLMExpansionDataSet u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  exact restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionDataSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_forall_expansionData`. -/
theorem convexAleksandrovNullBadSetStatement_of_forall_expansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ p : E, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  exact restrict_measure_secondOrderBadSet_eq_zero_of_forall_expansionData
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_forall_clmExpansionData`. -/
theorem convexAleksandrovNullBadSetStatement_of_forall_clmExpansionData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω →
        ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    ConvexAleksandrovNullBadSetStatement E Ω u := by
  intro hΩ hu
  exact restrict_measure_secondOrderBadSet_eq_zero_of_forall_hilbertClmExpansionData
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Final-assembly reduction from pointwise second-order differentiability on the whole domain.
This is useful for smooth or local-density routes that already produce the target predicate at
every point of the open convex domain. -/
theorem convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω → SecondOrderDifferentiableAt u x) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_forall_mem
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω → SecondOrderDifferentiableAt u x) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_forall_mem
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt`. -/
theorem convexAleksandrovNullBadSetStatement_of_forall_secondOrderDifferentiableAt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∀ ⦃x : E⦄, x ∈ Ω → SecondOrderDifferentiableAt u x) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt
      E Ω u hgood)

/-- Degenerate endpoint: on a subsingleton finite-dimensional real inner product space, the
convex Aleksandrov a.e. statement is immediate because every function is pointwise second-order
differentiable. -/
theorem convexAleksandrovAEStatement_of_subsingleton
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Subsingleton E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u := by
  exact convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt E Ω u
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_of_subsingleton u _)

/-- Null-bad-set version of `convexAleksandrovAEStatement_of_subsingleton`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_subsingleton
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Subsingleton E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  exact convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt E Ω u
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_of_subsingleton u _)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_subsingleton`. -/
theorem convexAleksandrovNullBadSetStatement_of_subsingleton
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Subsingleton E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_subsingleton E Ω u)

/-- Rank-zero finite-dimensional endpoint, stated with the usual `finrank` hypothesis. -/
theorem convexAleksandrovAEStatement_of_finrank_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 0) (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u := by
  exact convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt E Ω u
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_of_finrank_eq_zero hE u _)

/-- Null-bad-set version of `convexAleksandrovAEStatement_of_finrank_eq_zero`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_finrank_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 0) (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  exact convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt E Ω u
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_of_finrank_eq_zero hE u _)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_of_finrank_eq_zero`. -/
theorem convexAleksandrovNullBadSetStatement_of_finrank_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 0) (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_finrank_eq_zero E hE Ω u)

/-- Constant-function endpoint for the convex Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (c : ℝ) :
    ConvexAleksandrovAEStatement E Ω (fun _ : E => c) := by
  exact convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt E Ω
    (fun _ : E => c) (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_const c _)

/-- Null-bad-set version of `convexAleksandrovAEStatement_const`. -/
theorem convexAleksandrovNullBadSetOnStatement_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (c : ℝ) :
    ConvexAleksandrovNullBadSetOnStatement E Ω (fun _ : E => c) := by
  exact convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt E Ω
    (fun _ : E => c) (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_const c _)

/-- Restricted-measure null-bad-set version of `convexAleksandrovAEStatement_const`. -/
theorem convexAleksandrovNullBadSetStatement_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (c : ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω (fun _ : E => c) :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_const E Ω c)

/-- Affine-function endpoint for the convex Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_inner_add_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (p : E) (c : ℝ) :
    ConvexAleksandrovAEStatement E Ω (fun y : E => inner ℝ p y + c) := by
  exact convexAleksandrovAEStatement_of_forall_secondOrderDifferentiableAt E Ω
    (fun y : E => inner ℝ p y + c)
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_inner_add_const p c _)

/-- Null-bad-set version of `convexAleksandrovAEStatement_inner_add_const`. -/
theorem convexAleksandrovNullBadSetOnStatement_inner_add_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (p : E) (c : ℝ) :
    ConvexAleksandrovNullBadSetOnStatement E Ω (fun y : E => inner ℝ p y + c) := by
  exact convexAleksandrovNullBadSetOnStatement_of_forall_secondOrderDifferentiableAt E Ω
    (fun y : E => inner ℝ p y + c)
    (fun _hΩ _hu _x _hx => secondOrderDifferentiableAt_inner_add_const p c _)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovAEStatement_inner_add_const`. -/
theorem convexAleksandrovNullBadSetStatement_inner_add_const
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (p : E) (c : ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω (fun y : E => inner ℝ p y + c) :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_inner_add_const E Ω p c)

/-- Affine-function endpoint for the compatible finite-slice full-measure statement. -/
theorem compatibleDirectionalSliceFullMeasureStatement_inner_add_const
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (v : ι → E) (p : E) (c : ℝ) :
    CompatibleDirectionalSliceFullMeasureStatement D E Ω
      (fun y : E => inner ℝ p y + c) v := by
  intro _hΩ _hu
  rw [compatibleDirectionalSliceEstimateSet_inner_add_const]
  simp

/-- Affine-function endpoint for the compatible finite-slice quotient full-measure statement. -/
theorem compatibleDirectionalSliceQuotientFullMeasureStatement_inner_add_const
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (v : ι → E) (p : E) (c : ℝ) :
    CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω
      (fun y : E => inner ℝ p y + c) v := by
  intro _hΩ _hu
  rw [compatibleDirectionalSliceQuotientEstimateSet_inner_add_const]
  simp

/-- Affine-function endpoint for the symmetric-compatible finite-slice full-measure statement. -/
theorem symmetricCompatibleDirectionalSliceFullMeasureStatement_inner_add_const
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (v : ι → E) (p : E) (c : ℝ) :
    SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω
      (fun y : E => inner ℝ p y + c) v := by
  intro _hΩ _hu
  rw [symmetricCompatibleDirectionalSliceEstimateSet_inner_add_const]
  simp

/-- Affine-function endpoint for the symmetric-compatible finite-slice quotient full-measure
statement. -/
theorem symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_inner_add_const
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (v : ι → E) (p : E) (c : ℝ) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω
      (fun y : E => inner ℝ p y + c) v := by
  intro _hΩ _hu
  rw [symmetricCompatibleDirectionalSliceQuotientEstimateSet_inner_add_const]
  simp

end AleksandrovDifferentiability
