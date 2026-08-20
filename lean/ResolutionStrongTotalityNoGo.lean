import ResolutionStrongTotalityExactness

/-!
# No-go theorems for collapsing Resolution Answers to ordinary solutions

Strong Totality does not say that every specification is ordinarily solvable.
The residual constructor makes total Resolution semantics possible precisely
when no ordinary solution is available.  Therefore any attempted uniform
collapse from Resolution Answers back to ordinary solutions must fail.

The local theorem below shows the obstruction for every unsatisfiable
specification.  The global theorem then instantiates it with the false
proposition specification, ruling out a uniform extractor over all
specifications in `Specification.{0}`.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- An unsatisfiable specification admits no total extractor from its
Resolution Answer space to its ordinary solution space. -/
theorem unsatisfiable_no_resolutionAnswer_to_solution
    (S : Specification.{u})
    (hS : Not (Specification.Satisfiable S)) :
    Not (ResolutionAnswer S -> Specification.Solution S) := by
  intro extract
  let x : Specification.Solution S :=
    extract (ResolutionAnswer.residual : ResolutionAnswer S)
  exact hS ⟨x.1, x.2⟩

/-- There is no uniform operation which turns every Resolution Answer into an
ordinary solution of the same specification.  The false specification provides
the obstruction. -/
theorem no_uniform_resolutionAnswer_to_solution :
    Not ((S : Specification.{0}) ->
      ResolutionAnswer S -> Specification.Solution S) := by
  intro extract
  let x : Specification.Solution (propositionSpecification False) :=
    extract (propositionSpecification False)
      (ResolutionAnswer.residual :
        ResolutionAnswer (propositionSpecification False))
  exact x.2

/-- Equivalently, there cannot be a uniform witness that every well-formed
specification is ordinarily satisfiable.  Strong Totality is therefore
strictly a statement about Resolution Answers, not ordinary solutions. -/
theorem no_uniform_ordinary_solution :
    Not ((S : Specification.{0}) ->
      Nonempty (Specification.Solution S)) := by
  intro solve
  rcases solve (propositionSpecification False) with ⟨x⟩
  exact x.2

/-- In particular, the universal Strong Totality witness cannot be followed by
any uniform collapse to ordinary solutions. -/
theorem strongTotality_cannot_collapse_to_solutions :
    Not ((S : Specification.{0}) ->
      ResolutionAnswer S -> Specification.Solution S) :=
  no_uniform_resolutionAnswer_to_solution

end StrongTotality
end Resolution
