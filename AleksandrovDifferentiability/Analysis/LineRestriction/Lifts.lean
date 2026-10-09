module

public import AleksandrovDifferentiability.Analysis.LineRestriction.Basic

/-!
# Line subgradient lift interfaces
-/

@[expose] public section

open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def LineSubgradientLiftsToAmbient
    (s : Set E) (u : E → ℝ) (x z : E) (t q : ℝ) : Prop :=
  ∃ p : E, SubgradientOn s u (x + t • z) p ∧ q = inner ℝ p z

/-- Functional form of `LineSubgradientLiftsToAmbient`.

This is the form naturally produced by a geometric Hahn-Banach/separation argument: a continuous
linear functional supports the epigraph of `u` at `x + t • z` and has value `q` on the line
direction `z`.  In complete real inner-product spaces, Fréchet-Riesz converts this functional
form into the vector-valued subgradient form used elsewhere in the project. -/
def LineSubgradientLiftsToAmbientFunctional
    (s : Set E) (u : E → ℝ) (x z : E) (t q : ℝ) : Prop :=
  ∃ ℓ : StrongDual ℝ E,
    (∀ y ∈ s, u (x + t • z) + ℓ (y - (x + t • z)) ≤ u y) ∧ q = ℓ z

/-- A one-dimensional subgradient of a line restriction is exactly an affine minorant along that
line.  This is the line datum that the Hahn-Banach/separation step must extend to the ambient
domain. -/
theorem SubgradientOn.lineRestriction_supporting_slope_inequality
    {s : Set E} {u : E → ℝ} {x z : E} {t q r : ℝ}
    (hq : SubgradientOn (lineDomain s x z) (lineRestriction u x z) t q)
    (hr : r ∈ lineDomain s x z) :
    u (x + t • z) + q * (r - t) ≤ u (x + r • z) := by
  have h := hq.supporting_inequality (y := r) hr
  simpa [lineRestriction, Real.inner_apply, mul_comm] using h

/-- A functional lift gives the vector-valued ambient subgradient lift by Fréchet-Riesz. -/
theorem LineSubgradientLiftsToAmbientFunctional.to_lineSubgradientLiftsToAmbient
    [CompleteSpace E] {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (hmem : x + t • z ∈ s)
    (h : LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    LineSubgradientLiftsToAmbient s u x z t q := by
  rcases h with ⟨ℓ, hsupport, hq⟩
  let p : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  refine ⟨p, ⟨hmem, ?_⟩, ?_⟩
  · intro y hy
    simpa [p] using hsupport y hy
  · simpa [p] using hq

/-- Eventual version of the Fréchet-Riesz conversion from functional line-subgradient lifts to
vector-valued ambient subgradient lifts. -/
theorem eventually_lineSubgradientLiftsToAmbient_of_functional
    [CompleteSpace E] {s : Set E} {u : E → ℝ} {x : E}
    (hsegment : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q := by
  filter_upwards [hsegment, hlift] with z hzsegment hzlift t ht q hq
  exact (hzlift t ht q hq).to_lineSubgradientLiftsToAmbient (hzsegment t ht)

/-- If every one-dimensional subgradient along short segments lifts to an ambient subgradient,
then the right derivative of the line restriction is realized by an ambient subgradient.

This packages the already-formalized one-dimensional fact
`ConvexOn.lineRestriction_rightDeriv_subgradientOn_at`: at interior line parameters the right
derivative is itself a line subgradient. -/
theorem ConvexOn.eventually_lineRightDeriv_realized_by_subgradient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E,
          SubgradientOn s u (x + t • z) p ∧
            rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  have hline :
      SubgradientOn (lineDomain s x z)
        (AleksandrovDifferentiability.lineRestriction u x z) t
        (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
    ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
      (s := s) (u := u) (x := x) (v := z) (t := t) hu (hzsegment t ht)
  exact hzlift t ht (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) hline

end AleksandrovDifferentiability
