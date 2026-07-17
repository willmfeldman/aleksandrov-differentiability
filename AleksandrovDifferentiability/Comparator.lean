import AleksandrovDifferentiability
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Comparator challenges

This file gives a small API-regression smoke-test surface for the public import. The statements are
intentionally public-facing: they use the root import, the headline theorem, statement predicates,
the null-bad-set equivalence layer, the second-order witness interface, simple model cases, a
nontrivial Mathlib convex example, a nontrivial open-domain example, a
supremum-of-affine-functions challenge, the gradient bridge to Mathlib's Fréchet derivative, a
negative test on the absolute value, and a concrete non-vacuousness witness for the a.e. theorem.
-/

noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability.Comparator

/-- Challenge: the root import exposes the headline almost-everywhere theorem. -/
theorem challenge_root_import_headline_theorem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure E).restrict Ω), SecondOrderDifferentiableAt u x :=
  convexAleksandrovAE (E := E) (Ω := Ω) (u := u) hΩ hu

/-- Challenge: the statement-level interface is discharged by the exported theorem. -/
theorem challenge_statement_layer_headline_theorem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact convexAleksandrovAE (E := E) (Ω := Ω) (u := u) hΩ hu

/-- Challenge: the public statement layer includes the null-bad-set equivalence interface. -/
theorem challenge_null_bad_set_equivalence_interface
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u ↔
      ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u

/-- Challenge: the headline theorem can be stated using only Mathlib vocabulary after unfolding
the project-local second-order predicate. -/
theorem challenge_headline_in_mathlib_vocabulary
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure E).restrict Ω),
      ∃ p : E, ∃ B : E →L[ℝ] E,
        (∀ z w : E, inner ℝ (B z) w = inner ℝ z (B w)) ∧
          (fun z : E =>
              u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
            =o[𝓝 0] (fun z : E => ‖z‖ ^ 2) := by
  exact (convexAleksandrovAE (E := E) (Ω := Ω) (u := u) hΩ hu).mono fun _ hx => hx

/-- Challenge: the public predicate exposes gradient and symmetric Hessian witnesses. -/
theorem challenge_second_order_witness_interface
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {x : E} (h : SecondOrderDifferentiableAt u x) :
    ∃ p : E, ∃ B : E →L[ℝ] E,
      IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B :=
  h

/-- Sanity check: the project second-order expansion is literally the advertised little-o
quadratic remainder. -/
theorem challenge_second_order_expansion_is_littleO
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (x p : E) (B : E →L[ℝ] E) :
    HasSecondOrderExpansionAt u x p B ↔
      (fun z : E =>
          u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
        =o[𝓝 0] (fun z : E => ‖z‖ ^ 2) :=
  Iff.rfl

/-- Challenge: constant functions are second-order differentiable in the public sense. -/
theorem challenge_constant_model_case
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (x : E) :
    SecondOrderDifferentiableAt (fun _ : E => c) x :=
  secondOrderDifferentiableAt_const c x

/-- Challenge: affine functions represented by an inner-product slope have zero Hessian. -/
theorem challenge_affine_model_case
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p x : E) (c : ℝ) :
    SecondOrderDifferentiableAt (fun y : E => inner ℝ p y + c) x :=
  secondOrderDifferentiableAt_inner_add_const p c x

/-- Challenge: apply the headline theorem to Mathlib's nontrivial convex example `x ↦ ‖x‖`. -/
theorem challenge_mathlib_norm_convex_headline_theorem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    ∀ᵐ x ∂((volume : Measure E).restrict (Set.univ : Set E)),
      SecondOrderDifferentiableAt (fun y : E => ‖y‖) x := by
  exact convexAleksandrovAE
    (E := E) (Ω := Set.univ) (u := fun y : E => ‖y‖)
    isOpen_univ convexOn_univ_norm

/-- Challenge: apply the headline theorem on a concrete nonempty open convex domain, using
Mathlib's convexity of `x ↦ x ^ 2`. -/
theorem challenge_open_positive_square_headline_theorem :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
      SecondOrderDifferentiableAt (fun y : ℝ => y ^ 2) x := by
  have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun y : ℝ => y ^ 2) :=
    (convexOn_pow (𝕜 := ℝ) 2).subset Set.Ioi_subset_Ici_self (convex_Ioi (0 : ℝ))
  exact convexAleksandrovAE
    (E := ℝ) (Ω := Set.Ioi (0 : ℝ)) (u := fun y : ℝ => y ^ 2)
    isOpen_Ioi hconv

/-- Challenge: apply the headline theorem to a pointwise bounded supremum of affine functions. -/
theorem challenge_iSup_affine_family_headline_theorem
    {ι E : Type*} [Nonempty ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (p : ι → E) (b : ι → ℝ)
    (hBdd : ∀ x : E, BddAbove (Set.range fun i : ι => inner ℝ (p i) x + b i)) :
    ∀ᵐ x ∂((volume : Measure E).restrict (Set.univ : Set E)),
      SecondOrderDifferentiableAt
        (fun y : E => ⨆ i : ι, inner ℝ (p i) y + b i) x := by
  exact convexAleksandrovAE
    (E := E) (Ω := Set.univ)
    (u := fun y : E => ⨆ i : ι, inner ℝ (p i) y + b i)
    isOpen_univ (AleksandrovDifferentiability.convexOn_univ_iSup_inner_add p b hBdd)

/-- Challenge: the one-dimensional smooth sanity check remains available. -/
theorem challenge_smooth_one_dimensional_check :
    SmoothOneDimensionalScalarEstimateStatement :=
  smoothOneDimensionalScalarEstimateStatement

/-- Challenge: a second-order expansion yields Mathlib's Fréchet derivative, with the first-order
vector represented through the inner product. -/
theorem challenge_gradient_bridge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) :
    HasFDerivAt u (innerSL ℝ p) x :=
  h.hasFDerivAt

/-- Negative test: the predicate fails where it should. The absolute value is not even first-order
differentiable at `0`, so by the gradient bridge it is not second-order differentiable there. -/
theorem challenge_abs_not_second_order_differentiable :
    ¬ SecondOrderDifferentiableAt (fun y : ℝ => |y|) 0 := by
  rintro ⟨p, B, -, hExp⟩
  exact not_differentiableAt_abs_zero (challenge_gradient_bridge hExp).differentiableAt

/-- Existence: the a.e. statement is non-vacuous on a concrete domain. The open positive half-line
has nonzero volume, so the almost-everywhere conclusion produces an actual witness. -/
theorem challenge_exists_second_order_point :
    ∃ x ∈ Set.Ioi (0 : ℝ), SecondOrderDifferentiableAt (fun y : ℝ => y ^ 2) x := by
  have hae :
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
        x ∈ Set.Ioi (0 : ℝ) ∧ SecondOrderDifferentiableAt (fun y : ℝ => y ^ 2) x :=
    (ae_restrict_mem measurableSet_Ioi).and challenge_open_positive_square_headline_theorem
  have hne : ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) ≠ 0 := by
    simp [Measure.restrict_eq_zero, Real.volume_Ioi]
  haveI : (ae ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))).NeBot :=
    ae_neBot.mpr hne
  obtain ⟨x, hx, hdiff⟩ := hae.exists
  exact ⟨x, hx, hdiff⟩

end AleksandrovDifferentiability.Comparator
