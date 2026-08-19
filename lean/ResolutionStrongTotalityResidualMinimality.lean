import ResolutionStrongTotalityResidualStructure

/-!
# Minimal residual vocabulary for Strong Totality

`ResolutionAnswerWith S E` separates ordinary satisfying solutions from a
chosen residual vocabulary `E`.  This module gives the exact inhabitation
criterion and derives the sharp minimality statement behind uniform Strong
Totality.

For a fixed specification, a structured Resolution Answer exists exactly when
there is either an ordinary satisfying solution or at least one residual value.
Consequently, on every unsatisfiable specification, inhabitation of the answer
space is equivalent to inhabitation of the residual vocabulary itself.

The same criterion is forced on every universal residual extension, not merely
on the canonical constructor.  Moreover every universal residual extension is
canonically equivalent to `ResolutionAnswerWith S E`, with a unique equivalence
that preserves every ordinary solution and every individual residual value.
Hence a universal competitor cannot obtain extra hidden states or alter the
specified residual provenance while retaining the same universal property.

Thus one residual point is not merely sufficient for unconditional totality.
In the presence of any unsatisfiable specification it is also necessary.  The
canonical `Unit` residual therefore has the smallest possible nonempty shape
for a uniform total completion.
-/

universe u r

namespace Resolution
namespace StrongTotality

/-- Every universal residual extension has exactly the same inhabitation
criterion as the canonical structured answer space.  In particular,
universality itself prevents hidden states from making an otherwise empty
completion nonempty. -/
theorem universalResidualExtension_nonempty_iff
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Nonempty X ↔ Specification.Satisfiable S ∨ Nonempty E := by
  constructor
  · intro h
    rcases h with ⟨z⟩
    rcases hX
        (ResolutionAnswerWith S E)
        (@ResolutionAnswerWith.realize S E)
        (fun e : E =>
          (ResolutionAnswerWith.residual e : ResolutionAnswerWith S E)) with
      ⟨toCanonical, _, _⟩
    cases toCanonical z with
    | realized x hx =>
        exact Or.inl ⟨x, hx⟩
    | residual e =>
        exact Or.inr ⟨e⟩
  · intro h
    cases h with
    | inl hs =>
        rcases hs with ⟨x, hx⟩
        exact ⟨includeSolution ⟨x, hx⟩⟩
    | inr he =>
        rcases he with ⟨e⟩
        exact ⟨includeResidual e⟩

/-- A universal residual extension and the canonical structured answer space
are inhabited under exactly the same circumstances. -/
theorem universalResidualExtension_nonempty_iff_canonical
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Nonempty X ↔ Nonempty (ResolutionAnswerWith S E) := by
  exact (universalResidualExtension_nonempty_iff
    S E X includeSolution includeResidual hX).trans
      (resolutionAnswerWith_nonempty_iff S E).symm

/-- Structural canonicity for arbitrary residual provenance: every universal
residual extension admits a structure-preserving equivalence to the canonical
`ResolutionAnswerWith S E`, and every other equivalence preserving all ordinary
solutions and all residual values is equal to it. -/
theorem universalResidualExtension_unique_structural_equiv
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Exists fun e : Equiv X (ResolutionAnswerWith S E) =>
      ((forall x : Specification.Solution S,
          e (includeSolution x) = ResolutionAnswerWith.realize x) ∧
        (forall q : E,
          e (includeResidual q) =
            (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E))) ∧
      forall g : Equiv X (ResolutionAnswerWith S E),
        ((forall x : Specification.Solution S,
            g (includeSolution x) = ResolutionAnswerWith.realize x) ∧
          (forall q : E,
            g (includeResidual q) =
              (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E))) ->
        g = e := by
  rcases hX
      (ResolutionAnswerWith S E)
      (@ResolutionAnswerWith.realize S E)
      (fun q : E =>
        (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E)) with
    ⟨toCanonical, hto, htoUnique⟩
  rcases resolutionAnswerWith_isUniversalResidualExtension S E
      X includeSolution includeResidual with
    ⟨fromCanonical, hfrom, _⟩
  have hleft : forall z : X, fromCanonical (toCanonical z) = z := by
    have hcomp :
        ((forall x : Specification.Solution S,
            (fun z => fromCanonical (toCanonical z)) (includeSolution x) =
              includeSolution x) ∧
          (forall q : E,
            (fun z => fromCanonical (toCanonical z)) (includeResidual q) =
              includeResidual q)) := by
      constructor
      · intro x
        calc
          fromCanonical (toCanonical (includeSolution x)) =
              fromCanonical (ResolutionAnswerWith.realize x) :=
            congrArg fromCanonical (hto.1 x)
          _ = includeSolution x := hfrom.1 x
      · intro q
        calc
          fromCanonical (toCanonical (includeResidual q)) =
              fromCanonical
                (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) :=
            congrArg fromCanonical (hto.2 q)
          _ = includeResidual q := hfrom.2 q
    have hid :
        ((forall x : Specification.Solution S,
            (fun z : X => z) (includeSolution x) = includeSolution x) ∧
          (forall q : E,
            (fun z : X => z) (includeResidual q) = includeResidual q)) :=
      ⟨fun _ => rfl, fun _ => rfl⟩
    rcases hX X includeSolution includeResidual with ⟨f, _, huniq⟩
    have hc : (fun z => fromCanonical (toCanonical z)) = f :=
      huniq _ hcomp
    have hi : (fun z : X => z) = f := huniq _ hid
    intro z
    exact congrFun (hc.trans hi.symm) z
  have hright : forall a : ResolutionAnswerWith S E,
      toCanonical (fromCanonical a) = a := by
    intro a
    cases a with
    | realized x hx =>
        let sx : Specification.Solution S := ⟨x, hx⟩
        calc
          toCanonical (fromCanonical (.realized x hx)) =
              toCanonical (fromCanonical (ResolutionAnswerWith.realize sx)) := by
            rfl
          _ = toCanonical (includeSolution sx) :=
            congrArg toCanonical (hfrom.1 sx)
          _ = ResolutionAnswerWith.realize sx := hto.1 sx
          _ = .realized x hx := by rfl
    | residual q =>
        calc
          toCanonical (fromCanonical
              (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E)) =
              toCanonical (includeResidual q) :=
            congrArg toCanonical (hfrom.2 q)
          _ = (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E) :=
            hto.2 q
  let structural : Equiv X (ResolutionAnswerWith S E) := {
    toFun := toCanonical
    invFun := fromCanonical
    left_inv := hleft
    right_inv := hright
  }
  refine ⟨structural, hto, ?_⟩
  intro g hg
  have hgfun : g.toFun = toCanonical :=
    (htoUnique g.toFun hg).trans (htoUnique toCanonical hto).symm
  apply Equiv.ext
  change g.toFun = toCanonical
  exact hgfun

/-- The no-go form of residual minimality: for an unsatisfiable specification,
every universal residual extension is nonempty exactly when its residual
vocabulary is nonempty. -/
theorem unsatisfiable_universalResidualExtension_nonempty_iff
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual)
    (hS : Not (Specification.Satisfiable S)) :
    Nonempty X ↔ Nonempty E := by
  constructor
  · intro h
    have hcases := (universalResidualExtension_nonempty_iff
      S E X includeSolution includeResidual hX).1 h
    cases hcases with
    | inl hs =>
        exact False.elim (hS hs)
    | inr he =>
        exact he
  · intro he
    exact (universalResidualExtension_nonempty_iff
      S E X includeSolution includeResidual hX).2 (Or.inr he)

/-- Any inhabited universal total semantics for an unsatisfiable specification
therefore forces the residual vocabulary itself to be inhabited. -/
theorem unsatisfiable_universalResidualExtension_requires_residual
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual)
    (hS : Not (Specification.Satisfiable S))
    (hNonempty : Nonempty X) :
    Nonempty E :=
  (unsatisfiable_universalResidualExtension_nonempty_iff
    S E X includeSolution includeResidual hX hS).1 hNonempty

/-- Any inhabited residual vocabulary is sufficient to totalize every
specification, independently of whether that specification is satisfiable. -/
theorem residual_inhabited_sufficient_for_all
    (E : Type r)
    (hE : Nonempty E) :
    forall S : Specification.{u}, Nonempty (ResolutionAnswerWith S E) := by
  intro S
  rcases hE with ⟨e⟩
  exact strongTotalityWith S e

/-- If the universe contains one unsatisfiable specification, then a residual
vocabulary supports Strong Totality uniformly for all specifications exactly
when that residual vocabulary is inhabited. -/
theorem residual_inhabited_iff_uniformStrongTotality
    (S0 : Specification.{u})
    (hS0 : Not (Specification.Satisfiable S0))
    (E : Type r) :
    Nonempty E ↔
      forall S : Specification.{u}, Nonempty (ResolutionAnswerWith S E) := by
  constructor
  · intro hE
    exact residual_inhabited_sufficient_for_all E hE
  · intro hall
    exact (unsatisfiable_resolutionAnswerWith_nonempty_iff S0 E hS0).1
      (hall S0)

/-- The one-point residual vocabulary is uniformly sufficient.  Together with
`residual_inhabited_iff_uniformStrongTotality`, this records the literal
minimality of the canonical fallback shape: no empty residual vocabulary can
provide uniform totality in the presence of an unsatisfiable specification. -/
theorem unitResidual_uniformStrongTotality
    (S : Specification.{u}) :
    Nonempty (ResolutionAnswerWith S Unit) := by
  exact strongTotalityWith S ()

end StrongTotality
end Resolution
