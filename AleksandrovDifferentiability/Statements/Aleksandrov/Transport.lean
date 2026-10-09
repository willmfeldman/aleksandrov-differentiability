module

public import AleksandrovDifferentiability.Analysis.Directional.EstimateDefs
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Polarization
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.AmbientEstimate
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic
public import AleksandrovDifferentiability.Statements.Aleksandrov.Core
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Linear-isometry transport for Aleksandrov statement interfaces
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Pull a concrete second-order expansion back from an isometric coordinate model. -/
theorem HasSecondOrderExpansionAt.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {u : E → ℝ} {x : E} {p : F} {B : F →L[ℝ] F}
    (h : HasSecondOrderExpansionAt (u ∘ e.symm) (e x) p B) :
    HasSecondOrderExpansionAt u x (e.symm p) (linearIsometryEquivConjCLM e B) := by
  dsimp [HasSecondOrderExpansionAt] at h ⊢
  have htendsto : Filter.Tendsto (fun z : E => e z) (𝓝 0) (𝓝 0) := by
    simpa using (e.continuous.continuousAt (x := 0)).tendsto
  have hcomp := h.comp_tendsto htendsto
  refine (hcomp.congr_right ?_).congr_left ?_
  · intro z
    simp
  · intro z
    have hslope : inner ℝ p (e z) = inner ℝ (e.symm p) z := by
      simpa using (LinearIsometryEquiv.inner_map_map e (e.symm p) z)
    have hquad := inner_linearIsometryEquivConjCLM_self e B z
    simp [hslope, hquad]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Pull second-order differentiability back from an isometric coordinate model. -/
theorem SecondOrderDifferentiableAt.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {u : E → ℝ} {x : E}
    (h : SecondOrderDifferentiableAt (u ∘ e.symm) (e x)) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, B, hB, hquad⟩
  exact
    ⟨e.symm p, linearIsometryEquivConjCLM e B,
      isSymmetricOperator_linearIsometryEquivConjCLM e hB,
      hquad.of_image_linearIsometryEquiv e⟩

/-- Restricted volume is preserved by a linear isometry equivalence, with the domain carried to
its image. -/
theorem map_volume_restrict_linearIsometryEquiv_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) :
    ((volume : Measure E).restrict Ω).map e =
      (volume : Measure F).restrict (e '' Ω) := by
  have hpre : e ⁻¹' (e '' Ω) = Ω := by
    ext x
    simp
  calc
    ((volume : Measure E).restrict Ω).map e =
        ((volume : Measure E).restrict (e ⁻¹' (e '' Ω))).map e := by
          rw [hpre]
    _ = ((volume : Measure E).map e).restrict (e '' Ω) := by
          simpa using
            (e.toMeasurableEquiv.restrict_map (volume : Measure E) (e '' Ω)).symm
    _ = (volume : Measure F).restrict (e '' Ω) := by
          rw [(LinearIsometryEquiv.measurePreserving e).map_eq]

/-- Pull the final a.e. Aleksandrov statement back from an isometric coordinate model. -/
theorem ConvexAleksandrovAEStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovAEStatement F (e '' Ω) (u ∘ e.symm)) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hF := h hΩF huF
  have hmap :
      ((volume : Measure E).restrict Ω).map e =
        (volume : Measure F).restrict (e '' Ω) :=
    map_volume_restrict_linearIsometryEquiv_image e Ω
  have hpull :
      ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        SecondOrderDifferentiableAt (u ∘ e.symm) (e x) := by
    rw [← hmap] at hF
    exact e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hF
  exact hpull.mono fun x hx =>
    SecondOrderDifferentiableAt.of_image_linearIsometryEquiv (e := e) hx

end AleksandrovDifferentiability
