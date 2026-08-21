import ResolutionStrongTotalityUnifiedMorphisms

/-!
# Residual-semantics fibers for Strong Totality

The one-residual Strong Totality semantics is not terminal in the global space
of all specifications: a terminal object there would also require a canonical
validity-preserving translation from every mathematical specification into one
fixed specification, and no such translation exists in general.

The correct categorical statement is fiberwise.  Fix a mathematical
specification `S`.  Its residual semantics vary only by a residual vocabulary
`E`, with morphisms `E -> F`.  In this fiber, `Unit` is terminal.  The induced
map on Resolution Answers is exactly the canonical provenance-forgetting map.

Residual vocabularies may inhabit universes independent of the specification
and of one another.  In particular the minimal object uses literal `Unit` in
`Type 0`; no artificial universe lift is required.

This module records the category laws directly, without importing an external
category-theory library, so the result remains inside the repository's minimal
Lean dependency footprint.
-/

universe u r s t

namespace Resolution
namespace StrongTotality

/-- An object in the residual-semantics fiber over a fixed specification `S` is
just a choice of residual vocabulary. -/
structure ResidualFiberObject (S : Specification.{u}) where
  Residual : Type r

namespace ResidualFiberObject

/-- The minimal one-residual semantics object in every fiber.  Its residual
vocabulary is literally `Unit`, hence lives in universe zero. -/
def minimal (S : Specification.{u}) : ResidualFiberObject.{u, 0} S where
  Residual := Unit

end ResidualFiberObject

/-- Fiber morphisms preserve the mathematical specification and translate only
residual provenance.  Source and target residual universes are independent. -/
abbrev ResidualFiberHom
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S)
    (B : ResidualFiberObject.{u, s} S) : Type (max r s) :=
  ResidualRefinement A.Residual B.Residual

namespace ResidualFiberHom

/-- Identity fiber morphism. -/
def id
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S) : ResidualFiberHom A A :=
  ResidualRefinement.id A.Residual

/-- Composition of fiber morphisms. -/
def comp
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    {C : ResidualFiberObject.{u, t} S}
    (g : ResidualFiberHom B C)
    (f : ResidualFiberHom A B) : ResidualFiberHom A C :=
  ResidualRefinement.comp g f

@[simp] theorem comp_id
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    (f : ResidualFiberHom A B) :
    comp (id B) f = f := by
  rfl

@[simp] theorem id_comp
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    (f : ResidualFiberHom A B) :
    comp f (id A) = f := by
  rfl

@[simp] theorem comp_assoc
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    {C : ResidualFiberObject.{u, t} S}
    {D : ResidualFiberObject.{u, t} S}
    (h : ResidualFiberHom C D)
    (g : ResidualFiberHom B C)
    (f : ResidualFiberHom A B) :
    comp h (comp g f) = comp (comp h g) f := by
  rfl

end ResidualFiberHom

/-- Every fiber object has the canonical arrow to the minimal one-residual
object. -/
def residualFiberToMinimal
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S) :
    ResidualFiberHom A (ResidualFiberObject.minimal S) :=
  ResidualRefinement.toUnit A.Residual

/-- The arrow to the minimal object is unique.  This is the exact terminal
object property in the residual-semantics fiber over `S`. -/
theorem residualFiber_minimal_terminal
    (S : Specification.{u})
    (A : ResidualFiberObject.{u, r} S)
    (f : ResidualFiberHom A (ResidualFiberObject.minimal S)) :
    f = residualFiberToMinimal A := by
  exact ResidualRefinement.toUnit_unique A.Residual f

/-- Terminality in existence-and-uniqueness form. -/
theorem residualFiber_minimal_existsUnique
    (S : Specification.{u})
    (A : ResidualFiberObject.{u, r} S) :
    Exists fun f : ResidualFiberHom A (ResidualFiberObject.minimal S) =>
      forall g : ResidualFiberHom A (ResidualFiberObject.minimal S), g = f := by
  refine ⟨residualFiberToMinimal A, ?_⟩
  intro g
  exact residualFiber_minimal_terminal S A g

/-! ## Action of the fiber on Resolution Answers -/

/-- Each fiber object determines its structured Resolution Answer type. -/
abbrev ResidualFiberObject.Answer
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S) : Type (max u r) :=
  ResolutionAnswerWith S A.Residual

/-- A fiber morphism acts canonically on Resolution Answers. -/
def residualFiberMapAnswer
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    (f : ResidualFiberHom A B) :
    A.Answer -> B.Answer :=
  ResolutionAnswerWith.mapResidual f

@[simp] theorem residualFiberMapAnswer_id
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S)
    (a : A.Answer) :
    residualFiberMapAnswer (ResidualFiberHom.id A) a = a := by
  exact ResolutionAnswerWith.mapResidual_id a

@[simp] theorem residualFiberMapAnswer_comp
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    {C : ResidualFiberObject.{u, t} S}
    (g : ResidualFiberHom B C)
    (f : ResidualFiberHom A B)
    (a : A.Answer) :
    residualFiberMapAnswer (ResidualFiberHom.comp g f) a =
      residualFiberMapAnswer g (residualFiberMapAnswer f a) := by
  exact ResolutionAnswerWith.mapResidual_comp g f a

/-- The action of the unique terminal arrow is the structured one-point
coarsening, before identifying the one-point answer type with the original
minimal `ResolutionAnswer`. -/
theorem residualFiber_terminal_action
    (S : Specification.{u})
    (A : ResidualFiberObject.{u, r} S)
    (a : A.Answer) :
    unitResidualEquiv S
        (residualFiberMapAnswer (residualFiberToMinimal A) a) =
      coarsenResidual a := by
  exact coarsenResidual_eq_terminalMap S a

/-- Consequently, the original `ResolutionAnswer S` is the terminal semantic
image of every structured residual semantics in the fixed-specification fiber. -/
theorem residualFiber_terminal_semantics
    (S : Specification.{u})
    (A : ResidualFiberObject.{u, r} S) :
    Exists fun f : A.Answer -> ResolutionAnswer S =>
      f = coarsenResidual ∧
      forall g : A.Answer -> ResolutionAnswer S,
        ((forall x : Specification.Solution S,
            g (ResolutionAnswerWith.realize x) = realizeSolution x) ∧
          (forall e : A.Residual,
            g (.residual e) =
              (ResolutionAnswer.residual : ResolutionAnswer S))) ->
        g = f := by
  refine ⟨coarsenResidual, rfl, ?_⟩
  intro g hg
  rcases minimalResidualSemantics_terminal S A.Residual with
    ⟨terminal, hterminal, huniq⟩
  have hg' : g = terminal := huniq g hg
  have hc : coarsenResidual = terminal := by
    apply huniq coarsenResidual
    constructor
    · intro x
      cases x
      rfl
    · intro e
      rfl
  exact hg'.trans hc.symm

end StrongTotality
end Resolution
