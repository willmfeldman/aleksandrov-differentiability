module

public import AleksandrovDifferentiability.Analysis.LineRestriction
public import AleksandrovDifferentiability.Foundation.SecondOrder
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Quadratic trapping

This file records elementary trapping lemmas obtained by subtracting an affine function from a
convex function with a lower supporting hyperplane and an upper quadratic contact.
-/

@[expose] public section

namespace AleksandrovDifferentiability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The error after subtracting the affine function with slope `p` at `x`. -/
def affineRemainder (u : E → ℝ) (x p y : E) : ℝ :=
  u y - (u x + inner ℝ p (y - x))

@[simp]
theorem affineRemainder_self (u : E → ℝ) (x p : E) :
    affineRemainder u x p x = 0 := by
  simp [affineRemainder]

/-- The affine remainder, viewed as a function of increments `z` with `x + z ∈ s`, is convex
whenever `u` is convex on `s`.  This is the source proof's normalized function
`\tilde u(z) = u(x+z)-u(x)-p·z`. -/
theorem ConvexOn.affineRemainder_increment
    {s : Set E} {u : E → ℝ} {x p : E} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s)
      (fun z => affineRemainder u x p (x + z)) := by
  have htranslate :
      ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s) (fun z => u (x + z)) := by
    simpa [Function.comp_def] using hu.translate_right x
  have haffine :
      ConcaveOn ℝ ((fun z : E => x + z) ⁻¹' s) (fun z => u x + inner ℝ p z) := by
    refine ⟨htranslate.1, ?_⟩
    intro z _hz w _hw a b ha hb hab
    have hcombo :
        u x + inner ℝ p (a • z + b • w) =
          a * (u x + inner ℝ p z) + b * (u x + inner ℝ p w) := by
      have hux : u x = a * u x + b * u x := by
        calc
          u x = (a + b) * u x := by rw [hab]; ring
          _ = a * u x + b * u x := by ring
      calc
        u x + inner ℝ p (a • z + b • w)
            = u x + (a * inner ℝ p z + b * inner ℝ p w) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = a * (u x + inner ℝ p z) + b * (u x + inner ℝ p w) := by
              linarith
    exact le_of_eq hcombo.symm
  have hconv :
      ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s)
        (fun z => u (x + z) - (u x + inner ℝ p z)) :=
    htranslate.sub haffine
  refine hconv.congr ?_
  intro z _hz
  simp [affineRemainder]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A subgradient makes the affine remainder nonnegative on the domain. -/
theorem SubgradientOn.affineRemainder_nonneg
    {s : Set E} {u : E → ℝ} {x p y : E} (hp : SubgradientOn s u x p) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y := by
  dsimp [affineRemainder]
  exact sub_nonneg.mpr (hp.supporting_inequality (y := y) hy)

/-- Comparing a subgradient at `x1` with an arbitrary affine slope at `x0` is controlled by the
change in the affine remainder based at `x0`.

This is the algebraic core of the source proof's good-set gradient-control step. -/
theorem SubgradientOn.inner_sub_le_affineRemainder_sub
    {s : Set E} {u : E → ℝ} {x0 x1 p0 p1 y : E}
    (hp1 : SubgradientOn s u x1 p1) (hy : y ∈ s) :
    inner ℝ (p1 - p0) (y - x1) ≤
      affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 := by
  have hsupport := hp1.supporting_inequality (y := y) hy
  dsimp [affineRemainder]
  have hinner :
      inner ℝ (p1 - p0) (y - x1) =
        inner ℝ p1 (y - x1) - inner ℝ p0 (y - x1) := by
    rw [inner_sub_left]
  have hrem :
      affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 =
        (u y - u x1) - inner ℝ p0 (y - x1) := by
    have hinnerdiff :
        inner ℝ p0 (y - x0) - inner ℝ p0 (x1 - x0) =
          inner ℝ p0 (y - x1) := by
      rw [← inner_sub_right]
      congr 1
      abel
    dsimp [affineRemainder]
    linarith
  calc
    inner ℝ (p1 - p0) (y - x1)
        = inner ℝ p1 (y - x1) - inner ℝ p0 (y - x1) := hinner
    _ ≤ (u y - u x1) - inner ℝ p0 (y - x1) := by
      linarith
    _ = affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 := hrem.symm

/-- If the affine remainder based at `x0` is nonnegative at `x1`, then the preceding comparison
is bounded above by the affine remainder at `y`. -/
theorem SubgradientOn.inner_sub_le_affineRemainder_of_nonneg
    {s : Set E} {u : E → ℝ} {x0 x1 p0 p1 y : E}
    (hp1 : SubgradientOn s u x1 p1) (hy : y ∈ s)
    (h0 : 0 ≤ affineRemainder u x0 p0 x1) :
    inner ℝ (p1 - p0) (y - x1) ≤ affineRemainder u x0 p0 y := by
  have h := hp1.inner_sub_le_affineRemainder_sub (x0 := x0) (p0 := p0) hy
  linarith

/-- An upper contact with the same slope bounds the affine remainder by the quadratic opening. -/
theorem HasUpperContactWithSlopeOn.affineRemainder_le
    {s : Set E} {u : E → ℝ} {x p y : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hy : y ∈ s) :
    affineRemainder u x p y ≤ (a / 2) * ‖y - x‖ ^ 2 := by
  dsimp [affineRemainder]
  have hupper := h.upper_inequality (y := y) hy
  linarith

/-- If the same slope gives a lower support and an upper quadratic contact, then the affine
remainder is trapped between `0` and the quadratic opening. -/
theorem affineRemainder_nonneg_and_le_of_subgradient_of_upperContact
    {s : Set E} {u : E → ℝ} {x p y : E} {a : ℝ}
    (hp : SubgradientOn s u x p) (h : HasUpperContactWithSlopeOn s u x p a) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y ∧ affineRemainder u x p y ≤ (a / 2) * ‖y - x‖ ^ 2 :=
  ⟨hp.affineRemainder_nonneg hy, h.affineRemainder_le hy⟩

/-- Approximate quadratic trapping from a fixed-slope upper-contact opening bound. -/
theorem affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x p y : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hη : 0 < η) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y ∧
      affineRemainder u x p y ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 :=
  affineRemainder_nonneg_and_le_of_subgradient_of_upperContact hp
    (h.hasUpperContactWithSlopeOn_add_pos hη) hy

/-- For convex functions, a non-fixed upper-contact opening bound gives a single slope that
traps the affine remainder for every larger opening. -/
theorem exists_uniform_affineRemainder_trap_of_upperContactOpening_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u x p A ∧
          ∀ η : ℝ, 0 < η → ∀ y ∈ s,
            0 ≤ affineRemainder u x p y ∧
              affineRemainder u x p y ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη y hy
  exact affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening hp hfixed hη hy

/-- The affine remainder commutes with restricting to a line at an arbitrary line parameter. -/
theorem affineRemainder_lineRestriction_at (u : E → ℝ) (x p v : E) (t r : ℝ) :
    affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r =
      affineRemainder u (x + t • v) p (x + r • v) := by
  have hdiff : x + r • v - (x + t • v) = (r - t) • v := by
    calc
      x + r • v - (x + t • v) = r • v - t • v := by abel
      _ = (r - t) • v := by rw [sub_smul]
  simp [affineRemainder, AleksandrovDifferentiability.lineRestriction, hdiff,
    real_inner_smul_right]

end AleksandrovDifferentiability
