import ResolutionStrongTotalityResidualMinimality

/-!
# Classification of universal residual extensions

The universal property for structured Strong Totality is not merely satisfied
by the canonical construction `ResolutionAnswerWith S E`.  It characterizes
that construction completely.

A carrier `X` equipped with embeddings of ordinary solutions and residual
values is a universal residual extension exactly when it is structurally
equivalent to `ResolutionAnswerWith S E`: the equivalence must send each
included ordinary solution to its canonical realized answer and each included
residual value to the corresponding canonical residual answer.

Combining this converse with structural canonicity yields the stronger form:
the universal property is equivalent to the existence of a unique such
structure-preserving equivalence.
-/

universe u r

namespace Resolution
namespace StrongTotality

/-- An equivalence to the canonical structured answer space that preserves both
classes of generators: ordinary solutions and residual values. -/
def IsStructuralResidualEquiv
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (e : Equiv X (ResolutionAnswerWith S E)) : Prop :=
  (forall x : Specification.Solution S,
      e (includeSolution x) = ResolutionAnswerWith.realize x) ∧
    (forall q : E,
      e (includeResidual q) =
        (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E))

/-- Classification theorem: a structured extension is universal exactly when
it is structurally equivalent to the canonical `ResolutionAnswerWith S E`.
The reverse direction transports the canonical universal mapping property
through the supplied equivalence. -/
theorem universalResidualExtension_iff_structuralEquiv
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X) :
    IsUniversalResidualExtension S E X includeSolution includeResidual ↔
      Exists fun e : Equiv X (ResolutionAnswerWith S E) =>
        IsStructuralResidualEquiv
          S E X includeSolution includeResidual e := by
  constructor
  · intro hX
    rcases universalResidualExtension_unique_structural_equiv
        S E X includeSolution includeResidual hX with
      ⟨e, he, _⟩
    exact ⟨e, he⟩
  · intro hstruct
    rcases hstruct with ⟨e, he⟩
    intro Y onSolution onResidual
    rcases resolutionAnswerWith_isUniversalResidualExtension S E
        Y onSolution onResidual with
      ⟨canonicalMap, hcanonical, hcanonicalUnique⟩
    let f : X -> Y := fun z => canonicalMap (e z)
    refine ⟨f, ?_, ?_⟩
    · constructor
      · intro x
        calc
          f (includeSolution x) = canonicalMap (e (includeSolution x)) := by
            rfl
          _ = canonicalMap (ResolutionAnswerWith.realize x) :=
            congrArg canonicalMap (he.1 x)
          _ = onSolution x := hcanonical.1 x
      · intro q
        calc
          f (includeResidual q) = canonicalMap (e (includeResidual q)) := by
            rfl
          _ = canonicalMap
              (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) :=
            congrArg canonicalMap (he.2 q)
          _ = onResidual q := hcanonical.2 q
    · intro g hg
      let gCanonical : ResolutionAnswerWith S E -> Y :=
        fun a => g (e.invFun a)
      have hgCanonical :
          ((forall x : Specification.Solution S,
              gCanonical (ResolutionAnswerWith.realize x) = onSolution x) ∧
            (forall q : E,
              gCanonical
                  (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) =
                onResidual q)) := by
        constructor
        · intro x
          have hinv :
              e.invFun (ResolutionAnswerWith.realize x) = includeSolution x := by
            calc
              e.invFun (ResolutionAnswerWith.realize x) =
                  e.invFun (e (includeSolution x)) :=
                congrArg e.invFun (he.1 x).symm
              _ = includeSolution x := e.left_inv (includeSolution x)
          calc
            gCanonical (ResolutionAnswerWith.realize x) =
                g (e.invFun (ResolutionAnswerWith.realize x)) := by rfl
            _ = g (includeSolution x) := congrArg g hinv
            _ = onSolution x := hg.1 x
        · intro q
          have hinv :
              e.invFun
                  (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) =
                includeResidual q := by
            calc
              e.invFun
                  (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) =
                  e.invFun (e (includeResidual q)) :=
                congrArg e.invFun (he.2 q).symm
              _ = includeResidual q := e.left_inv (includeResidual q)
          calc
            gCanonical
                (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) =
                g (e.invFun
                  (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E)) := by
              rfl
            _ = g (includeResidual q) := congrArg g hinv
            _ = onResidual q := hg.2 q
      have hcanonicalEq : gCanonical = canonicalMap :=
        hcanonicalUnique gCanonical hgCanonical
      funext z
      calc
        g z = g (e.invFun (e z)) := congrArg g (e.left_inv z).symm
        _ = gCanonical (e z) := by rfl
        _ = canonicalMap (e z) := congrFun hcanonicalEq (e z)
        _ = f z := by rfl

/-- Strong classification: universality is equivalent to the existence of a
unique structure-preserving equivalence with the canonical structured answer
space.  Thus the universal property determines the carrier up to one and only
one equivalence compatible with its generators. -/
theorem universalResidualExtension_iff_unique_structuralEquiv
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X) :
    IsUniversalResidualExtension S E X includeSolution includeResidual ↔
      Exists fun e : Equiv X (ResolutionAnswerWith S E) =>
        IsStructuralResidualEquiv
            S E X includeSolution includeResidual e ∧
          forall g : Equiv X (ResolutionAnswerWith S E),
            IsStructuralResidualEquiv
                S E X includeSolution includeResidual g ->
              g = e := by
  constructor
  · intro hX
    rcases universalResidualExtension_unique_structural_equiv
        S E X includeSolution includeResidual hX with
      ⟨e, he, hunique⟩
    exact ⟨e, he, hunique⟩
  · intro h
    rcases h with ⟨e, he, _⟩
    exact (universalResidualExtension_iff_structuralEquiv
      S E X includeSolution includeResidual).2 ⟨e, he⟩

end StrongTotality
end Resolution
