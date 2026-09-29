import Statement
import AleksandrovDifferentiability
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

theorem challenge_bounded_abs_headline : BoundedAbsHeadlineStatement.Claim := by
  unfold BoundedAbsHeadlineStatement.Claim
  have hae :
      ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
        BoundedAbsHeadlineStatement.SecondOrderDifferentiableAt (fun y : ℝ => |y|) x := by
    have hconv : ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (fun y : ℝ => |y|) := by
      exact (convexOn_univ_norm (E := ℝ)).subset (Set.subset_univ _) (convex_Ioo (-1 : ℝ) 1)
    exact convexAleksandrovAE
      (E := ℝ) (Ω := Set.Ioo (-1 : ℝ) 1) (u := fun y : ℝ => |y|)
      isOpen_Ioo hconv
  refine ⟨hae, ?_, ?_⟩
  · rintro ⟨p, B, -, hExp⟩
    change HasSecondOrderExpansionAt (fun y : ℝ => |y|) 0 p B at hExp
    exact not_differentiableAt_abs_zero hExp.hasFDerivAt.differentiableAt
  · have hmemdiff :
        ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
          x ∈ Set.Ioo (-1 : ℝ) 1 ∧
            BoundedAbsHeadlineStatement.SecondOrderDifferentiableAt (fun y : ℝ => |y|) x :=
      (ae_restrict_mem measurableSet_Ioo).and hae
    have hne : (volume.restrict (Set.Ioo (-1 : ℝ) 1) : Measure ℝ) ≠ 0 := by
      simp [Measure.restrict_eq_zero, Real.volume_Ioo]
    have : (ae (volume.restrict (Set.Ioo (-1 : ℝ) 1) : Measure ℝ)).NeBot :=
      ae_neBot.mpr hne
    exact hmemdiff.exists

end AleksandrovDifferentiability
