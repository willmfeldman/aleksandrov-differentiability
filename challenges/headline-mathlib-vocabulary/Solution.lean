module

public import Vocabulary
public import AleksandrovDifferentiability

@[expose] public noncomputable section

open Asymptotics
open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

theorem challenge_headline_in_mathlib_vocabulary :
    HeadlineMathlibVocabularyStatement.Claim := by
  unfold HeadlineMathlibVocabularyStatement.Claim
  intro E _ _ _ _ _ Ω u hΩ hu
  exact (convexAleksandrovAE (E := E) (Ω := Ω) (u := u) hΩ hu).mono fun _ hx => hx

end AleksandrovDifferentiability
