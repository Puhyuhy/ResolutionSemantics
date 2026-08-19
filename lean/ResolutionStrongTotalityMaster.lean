import ResolutionStrongTotalityMinimality

/-!
# Master theorem package for Strong Totality

This module records the central principle proved by the Strong Totality
research layer:

  every well-formed mathematical specification has a Resolution Answer.

The statement is intentionally stronger than evaluator totality and weaker than
ordinary satisfiability.  A false or unsatisfiable specification need not have
an ordinary solution; it still has a typed residual Resolution Answer.

The surrounding theorems record the properties already established for the
canonical completion: exactness with respect to satisfiability, universality,
rigidity/minimality, structural canonicity, naturality, representation
invariance, dependent closure, and agreement with the existing kernel/free-
algebra layer.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- The foundational Strong Totality principle in its most direct form. -/
theorem strongTotality_master
    (S : Specification.{u}) :
    Nonempty (ResolutionAnswer S) :=
  strongTotality S

/-- Exactness of the master principle: ordinary satisfiability is precisely the
existence of a non-residual Resolution Answer.  Strong Totality therefore adds
total semantics without manufacturing ordinary solutions. -/
theorem strongTotality_master_exact
    (S : Specification.{u}) :
    Specification.Satisfiable S ↔
      Exists fun a : ResolutionAnswer S =>
        a ≠ (ResolutionAnswer.residual : ResolutionAnswer S) :=
  satisfiable_iff_exists_nonresidual S

/-- In the unsatisfiable case the residual answer is not merely available: it
is the unique Resolution Answer. -/
theorem strongTotality_master_unsatisfiable_unique
    (S : Specification.{u}) :
    Not (Specification.Satisfiable S) ↔
      forall a : ResolutionAnswer S,
        a = (ResolutionAnswer.residual : ResolutionAnswer S) :=
  not_satisfiable_iff_all_residual S

/-- Any universal pointed totalization is rigid: ordinary solutions remain
injectively embedded, none can collapse to the residual, and there are no
additional hidden states beyond those images and the single residual point. -/
theorem strongTotality_master_rigid
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    Function.Injective includeSolution ∧
      (forall x : Specification.Solution S, includeSolution x ≠ residual) ∧
      (forall z : X,
        (Exists fun x : Specification.Solution S => z = includeSolution x) ∨
        z = residual) :=
  universalTotalization_rigid S X includeSolution residual hX

/-- Structural canonicity: every universal pointed totalization has one
structure-preserving equivalence to the canonical Resolution Answer space, and
any other equivalence preserving the same solution and residual generators is
identical to it. -/
theorem strongTotality_master_canonical
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    Exists fun e : Equiv X (ResolutionAnswer S) =>
      ((forall x : Specification.Solution S,
          e (includeSolution x) = realizeSolution x) ∧
        e residual = (ResolutionAnswer.residual : ResolutionAnswer S)) ∧
      forall g : Equiv X (ResolutionAnswer S),
        ((forall x : Specification.Solution S,
            g (includeSolution x) = realizeSolution x) ∧
          g residual = (ResolutionAnswer.residual : ResolutionAnswer S)) ->
        g = e :=
  universalTotalization_unique_structural_equiv
    S X includeSolution residual hX

/-- Operation-family form: every input of every well-formed dependent
mathematical operation specification has a Resolution Answer. -/
theorem strongTotality_master_operation
    {I : Type v}
    {O : I -> Type u}
    (R : (i : I) -> O i -> Prop)
    (i : I) :
    Nonempty (ResolutionAnswer (operationSpecification R i)) :=
  operationStrongTotality R i

/-- False is not ordinarily satisfiable when viewed as a proposition
specification. -/
theorem falseSpecification_not_satisfiable :
    Not (Specification.Satisfiable (propositionSpecification False)) := by
  intro h
  rcases h with ⟨x, hx⟩
  exact hx

/-- Nevertheless even the false specification has a Resolution Answer.  This
fixes the intended meaning of Strong Totality: total Resolution semantics does
not assert that every specification has an ordinary satisfying solution. -/
theorem falseSpecification_has_resolutionAnswer :
    Nonempty (ResolutionAnswer (propositionSpecification False)) :=
  propositionStrongTotality False

/-- The false specification has exactly one Resolution Answer: the residual
point. -/
theorem falseSpecification_resolutionAnswer_unique :
    forall a : ResolutionAnswer (propositionSpecification False),
      a = (ResolutionAnswer.residual :
        ResolutionAnswer (propositionSpecification False)) :=
  (not_satisfiable_iff_all_residual (propositionSpecification False)).1
    falseSpecification_not_satisfiable

/-- The canonical answer construction has the universal free-pointed
completion property. -/
theorem strongTotality_master_universal
    (S : Specification.{u}) :
    IsUniversalTotalization S (ResolutionAnswer S)
      (@realizeSolution S) .residual :=
  resolutionAnswer_isUniversalTotalization S

/-- The canonical completion is initial among pointed completions of the same
specification. -/
theorem strongTotality_master_initial
    (S : Specification.{u})
    (A : CompletionObject S) :
    Exists fun f : CompletionHom (canonicalCompletion S) A =>
      forall g : CompletionHom (canonicalCompletion S) A, g = f :=
  canonicalCompletion_initial S A

/-- Strong Totality is natural under every validity-preserving translation of
specifications. -/
theorem strongTotality_master_natural
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    Exists fun p : CompletionHomOver f
        (canonicalCompletion S) (canonicalCompletion T) =>
      forall q : CompletionHomOver f
          (canonicalCompletion S) (canonicalCompletion T),
        q = p :=
  strongTotality_universalNatural f

/-- Equivalent presentations of the same mathematical specification induce
equivalent Resolution Answer spaces. -/
theorem strongTotality_master_representationInvariant
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Nonempty (Equiv (ResolutionAnswer S) (ResolutionAnswer T)) :=
  SpecEquiv.strongTotality_representationInvariant e

/-- Strong Totality is closed under genuinely dependent mathematical
construction. -/
theorem strongTotality_master_dependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Nonempty (ResolutionAnswer (dependentSpecification S T)) :=
  dependentStrongTotality S T

/-- The pre-existing kernel evaluator is a provenance-preserving structured
Strong Totality semantics for every concrete expression. -/
theorem strongTotality_master_kernel
    {Sigma : Signature.{u}}
    (D : PartialAlg Sigma)
    (e : Expr Sigma D.Carrier) :
    Nonempty (ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier)) :=
  kernel_isStructuredStrongTotality D e

/-- The generated free Resolution algebra is exactly equivalent to the
structured Strong Totality presentation which separates generated old answers
from generated suspension provenance. -/
def strongTotality_master_freeEquiv
    {Sigma : Signature.{u}}
    (D : PartialAlg Sigma) :
    Equiv (Free.GeneratedAns D) (GeneratedStrongAnswer D) :=
  generatedAnsEquivStrong D

/-- The Strong Totality presentation of the generated free algebra retains the
same free-algebra universal mapping property. -/
theorem strongTotality_master_freeUniversal
    {Sigma : Signature.{u}}
    (D : PartialAlg Sigma)
    (T : Free.CompatibleAlg D) :
    Exists fun F : StrongCompatibleHom D T =>
      forall G : StrongCompatibleHom D T, G = F :=
  generatedStrong_has_unique_compatibleHom D T

end StrongTotality
end Resolution
