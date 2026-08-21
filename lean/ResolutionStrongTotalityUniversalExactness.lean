import ResolutionStrongTotalityStructuredExactness

/-!
# Exactness on arbitrary universal Strong Totality carriers

The canonical structured answer type already separates ordinary solutions from
residual provenance exactly.  The classification theorem lets us transfer that
separation to every carrier satisfying the same universal property.

For an arbitrary universal residual extension `X`, the supplied solution map
and residual map are both injective, their images are disjoint, and together
they exhaust the carrier.  Hence no universal presentation can hide additional
states, identify two distinct residual provenance values, identify two distinct
ordinary solutions, or collapse an ordinary solution into a residual state.

This gives exactness intrinsically on `X`: satisfiability is equivalent to the
existence of a point in the included-solution image, while unsatisfiability is
equivalent to every point lying in the included-residual image.
-/

universe u r w

namespace Resolution
namespace StrongTotality

namespace ResolutionAnswerWith

/-- Canonical realization preserves distinct certified solutions. -/
theorem realize_injective
    (S : Specification.{u})
    (E : Type r) :
    Function.Injective (@realize S E) := by
  intro x y h
  cases x with
  | mk x hx =>
      cases y with
      | mk y hy =>
          cases h
          rfl

/-- Canonical residual inclusion preserves distinct provenance values. -/
theorem residual_injective
    (S : Specification.{u})
    (E : Type r) :
    Function.Injective
      (fun q : E =>
        (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E)) := by
  intro q p h
  cases h
  rfl

/-- A canonical realized answer can never equal a canonical residual answer. -/
theorem realize_ne_residual
    (S : Specification.{u})
    (E : Type r)
    (x : Specification.Solution S)
    (q : E) :
    realize x ≠ (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) := by
  intro h
  cases x with
  | mk x hx =>
      cases h

end ResolutionAnswerWith

/-- A point of an arbitrary carrier is solution-realized when it belongs to the
image of the carrier's designated solution inclusion. -/
def IsIncludedSolution
    {S : Specification.{u}}
    {X : Type w}
    (includeSolution : Specification.Solution S -> X)
    (z : X) : Prop :=
  Exists fun x : Specification.Solution S => z = includeSolution x

/-- A point of an arbitrary carrier is residual when it belongs to the image of
the carrier's designated residual inclusion. -/
def IsIncludedResidual
    {E : Type r}
    {X : Type w}
    (includeResidual : E -> X)
    (z : X) : Prop :=
  Exists fun q : E => z = includeResidual q

/-- Rigidity on every universal structured carrier: solution and residual
inclusions are injective, their images are disjoint, and those two images
exhaust the carrier. -/
theorem universalResidualExtension_rigid
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Function.Injective includeSolution ∧
      Function.Injective includeResidual ∧
      (forall x : Specification.Solution S, forall q : E,
        includeSolution x ≠ includeResidual q) ∧
      (forall z : X,
        IsIncludedSolution includeSolution z ∨
          IsIncludedResidual includeResidual z) := by
  rcases universalResidualExtension_unique_structural_equiv
      S E X includeSolution includeResidual hX with
    ⟨e, he, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply ResolutionAnswerWith.realize_injective S E
    calc
      ResolutionAnswerWith.realize x = e (includeSolution x) :=
        (he.1 x).symm
      _ = e (includeSolution y) := congrArg e hxy
      _ = ResolutionAnswerWith.realize y := he.1 y
  · intro q p hqp
    apply ResolutionAnswerWith.residual_injective S E
    calc
      (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) =
          e (includeResidual q) := (he.2 q).symm
      _ = e (includeResidual p) := congrArg e hqp
      _ = (ResolutionAnswerWith.residual p : ResolutionAnswerWith S E) :=
        he.2 p
  · intro x q hxq
    apply ResolutionAnswerWith.realize_ne_residual S E x q
    calc
      ResolutionAnswerWith.realize x = e (includeSolution x) :=
        (he.1 x).symm
      _ = e (includeResidual q) := congrArg e hxq
      _ = (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) :=
        he.2 q
  · intro z
    have hclass := ResolutionAnswerWith.realized_or_residual (e z)
    cases hclass with
    | inl hrealized =>
        rcases hrealized with ⟨x, hx⟩
        have heq : e z = e (includeSolution x) := by
          calc
            e z = ResolutionAnswerWith.realize x := hx
            _ = e (includeSolution x) := (he.1 x).symm
        have hz : z = includeSolution x := by
          calc
            z = e.invFun (e z) := (e.left_inv z).symm
            _ = e.invFun (e (includeSolution x)) :=
              congrArg e.invFun heq
            _ = includeSolution x := e.left_inv (includeSolution x)
        exact Or.inl ⟨x, hz⟩
    | inr hresidual =>
        rcases hresidual with ⟨q, hq⟩
        have heq : e z = e (includeResidual q) := by
          calc
            e z = (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) :=
              hq
            _ = e (includeResidual q) := (he.2 q).symm
        have hz : z = includeResidual q := by
          calc
            z = e.invFun (e z) := (e.left_inv z).symm
            _ = e.invFun (e (includeResidual q)) :=
              congrArg e.invFun heq
            _ = includeResidual q := e.left_inv (includeResidual q)
        exact Or.inr ⟨q, hz⟩

/-- Satisfiability is already visible intrinsically in any designated solution
inclusion: it is exactly the existence of a carrier point in that image. -/
theorem satisfiable_iff_exists_includedSolution
    (S : Specification.{u})
    (X : Type w)
    (includeSolution : Specification.Solution S -> X) :
    Specification.Satisfiable S ↔
      Exists fun z : X => IsIncludedSolution includeSolution z := by
  constructor
  · intro hS
    rcases hS with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    exact ⟨includeSolution sx, sx, rfl⟩
  · intro h
    rcases h with ⟨z, x, _⟩
    exact ⟨x.1, x.2⟩

/-- Universal-carrier exactness: unsatisfiability is exactly the statement that
every point of the universal carrier is residual. -/
theorem universalResidualExtension_not_satisfiable_iff_all_includedResidual
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Not (Specification.Satisfiable S) ↔
      forall z : X, IsIncludedResidual includeResidual z := by
  have hrigid := universalResidualExtension_rigid
    S E X includeSolution includeResidual hX
  constructor
  · intro hS z
    have hz := hrigid.2.2.2 z
    cases hz with
    | inl hsolution =>
        rcases hsolution with ⟨x, _⟩
        exact False.elim (hS ⟨x.1, x.2⟩)
    | inr hresidual =>
        exact hresidual
  · intro hall hS
    rcases hS with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    rcases hall (includeSolution sx) with ⟨q, hq⟩
    exact hrigid.2.2.1 sx q hq

/-- Pointwise partition form: on a universal carrier every point is exactly one
of solution-realized or residual. -/
theorem universalResidualExtension_answer_partition
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual)
    (z : X) :
    (IsIncludedSolution includeSolution z ∨
      IsIncludedResidual includeResidual z) ∧
    Not (IsIncludedSolution includeSolution z ∧
      IsIncludedResidual includeResidual z) := by
  have hrigid := universalResidualExtension_rigid
    S E X includeSolution includeResidual hX
  constructor
  · exact hrigid.2.2.2 z
  · intro hboth
    rcases hboth.1 with ⟨x, hx⟩
    rcases hboth.2 with ⟨q, hq⟩
    have hcross : includeSolution x = includeResidual q := hx.symm.trans hq
    exact hrigid.2.2.1 x q hcross

/-- Exactness package for an arbitrary universal carrier. -/
theorem universalResidualExtension_exact
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    (Specification.Satisfiable S ↔
      Exists fun z : X => IsIncludedSolution includeSolution z) ∧
    (Not (Specification.Satisfiable S) ↔
      forall z : X, IsIncludedResidual includeResidual z) :=
  ⟨satisfiable_iff_exists_includedSolution S X includeSolution,
    universalResidualExtension_not_satisfiable_iff_all_includedResidual
      S E X includeSolution includeResidual hX⟩

end StrongTotality
end Resolution
