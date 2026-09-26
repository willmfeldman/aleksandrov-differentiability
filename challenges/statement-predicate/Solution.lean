import Statement
import AleksandrovDifferentiability

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem challenge_statement_predicate : StatementPredicateStatement.Claim := by
  unfold StatementPredicateStatement.Claim
  intro E _ _ _ _ _ Ω u hΩ hu
  exact convexAleksandrovAEStatement E Ω u hΩ hu

end AleksandrovDifferentiability
