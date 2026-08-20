import ResolutionStrongTotalityMinimality
import ResolutionStrongTotalityResidualClassification
import ResolutionStrongTotalityFamilyUniversal
import ResolutionStrongTotalityFamilyNaturality
import ResolutionStrongTotalityFamilyInitiality

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
rigidity/minimality, structural canonicity, residual classification, naturality,
representation invariance, dependent closure, and agreement with the existing
kernel/free-algebra layer.
-/

universe u v w r

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

/-- Global family universality: the canonical Resolution construction satisfies
one simultaneous universal property over every member of an arbitrary family
of well-formed specifications. -/
theorem strongTotality_master_familyUniversal
    {I : Type v}
    (F : I -> Specification.{u}) :
    IsUniversalTotalizationFamily F
      (fun i => ResolutionAnswer (F i))
      (fun i => @realizeSolution (F i))
      (fun i =>
        (ResolutionAnswer.residual : ResolutionAnswer (F i))) :=
  resolutionAnswerFamily_isUniversalTotalization F

/-- Global family canonicity: every simultaneous universal totalization of an
arbitrary specification family is uniquely structurally equivalent to the
canonical Resolution family.  The equivalences are chosen and characterized as
one dependent family, rather than by unrelated pointwise existence claims. -/
theorem strongTotality_master_familyCanonical
    {I : Type v}
    (F : I -> Specification.{u})
    (X : I -> Type u)
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (residual : (i : I) -> X i)
    (hX : IsUniversalTotalizationFamily F X includeSolution residual) :
    Exists fun e : (i : I) -> Equiv (X i) (ResolutionAnswer (F i)) =>
      ((forall (i : I) (x : Specification.Solution (F i)),
          e i (includeSolution i x) = realizeSolution x) ∧
        (forall i : I,
          e i (residual i) =
            (ResolutionAnswer.residual : ResolutionAnswer (F i)))) ∧
      forall g : (i : I) -> Equiv (X i) (ResolutionAnswer (F i)),
        ((forall (i : I) (x : Specification.Solution (F i)),
            g i (includeSolution i x) = realizeSolution x) ∧
          (forall i : I,
            g i (residual i) =
              (ResolutionAnswer.residual : ResolutionAnswer (F i)))) ->
        g = e :=
  universalTotalizationFamily_unique_structural_equiv
    F X includeSolution residual hX

/-- Exact family classification: a packaged family completion satisfies Strong
Totality's simultaneous universal property exactly when it admits one unique
structural equivalence to the canonical Resolution family. -/
theorem strongTotality_master_familyClassification
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F) :
    IsUniversalFamilyCompletion F A ↔
      Exists fun e : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
        IsCanonicalFamilyEquiv F A e ∧
        forall g : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)),
          IsCanonicalFamilyEquiv F A g -> g = e :=
  universalFamilyCompletion_iff_uniqueCanonicalEquiv F A

/-- Categorical family classification: Strong Totality's simultaneous universal
property is exactly initiality among pointed completions of the same
specification family.  Hence the universal extension formulation and the
categorical formulation are not merely compatible; they are equivalent. -/
theorem strongTotality_master_familyInitiality
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F) :
    IsUniversalFamilyCompletion F A ↔
      forall B : FamilyCompletionObject F,
        Exists fun p : FamilyCompletionHomOver
            (FamilySpecMorphism.id F) A B =>
          forall q : FamilyCompletionHomOver
              (FamilySpecMorphism.id F) A B,
            q = p :=
  universalFamilyCompletion_iff_initial F A

/-- Global family naturality with reindexing: universal source and target
families admit unique structural equivalences to the canonical Resolution
families and one unique map over every reindexed family translation.  These
unique data necessarily commute with the fiberwise `ResolutionAnswer.map`
action at every source index. -/
theorem strongTotality_master_familyCanonicalNatural
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (hA : IsUniversalFamilyCompletion F A)
    (hB : IsUniversalFamilyCompletion G B) :
    Exists fun eF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
      IsCanonicalFamilyEquiv F A eF ∧
      (forall gF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)),
        IsCanonicalFamilyEquiv F A gF -> gF = eF) ∧
      Exists fun eG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)) =>
        IsCanonicalFamilyEquiv G B eG ∧
        (forall gG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)),
          IsCanonicalFamilyEquiv G B gG -> gG = eG) ∧
        Exists fun p : FamilyCompletionHomOver eta A B =>
          (forall q : FamilyCompletionHomOver eta A B, q = p) ∧
          forall (i : I) (x : A.Carrier i),
            eG (eta.index i) (p.toFun i x) =
              ResolutionAnswer.map (eta.mapSpec i) (eF i x) :=
  universalFamilies_canonicalNatural eta A B hA hB

/-- Full classification for arbitrary residual provenance: a carrier is a
universal residual extension exactly when there exists one and only one
equivalence to the canonical structured answer space that preserves every
ordinary-solution generator and every residual generator. -/
theorem strongTotality_master_residualClassification
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
              g = e :=
  universalResidualExtension_iff_unique_structuralEquiv
    S E X includeSolution includeResidual

/-- Exact residual existence criterion: a structured answer exists precisely
when either an ordinary solution exists or the chosen residual vocabulary has
an inhabitant. -/
theorem strongTotality_master_residualExistence
    (S : Specification.{u})
    (E : Type r) :
    Nonempty (ResolutionAnswerWith S E) ↔
      Specification.Satisfiable S ∨ Nonempty E :=
  resolutionAnswerWith_nonempty_iff S E

/-- On an unsatisfiable specification, residual inhabitation is necessary and
sufficient for Strong Totality.  No residual-free completion can evade this
obstruction. -/
theorem strongTotality_master_unsatisfiableResidualMinimal
    (S : Specification.{u})
    (E : Type r)
    (hS : Not (Specification.Satisfiable S)) :
    Nonempty (ResolutionAnswerWith S E) ↔ Nonempty E :=
  unsatisfiable_resolutionAnswerWith_nonempty_iff S E hS

/-- Literal no-go theorem: an empty residual vocabulary cannot totalize any
unsatisfiable specification. -/
theorem strongTotality_master_emptyResidual_noGo
    (S : Specification.{u})
    (hS : Not (Specification.Satisfiable S)) :
    Not (Nonempty (ResolutionAnswerWith S Empty)) :=
  unsatisfiable_emptyResidual_not_total S hS

/-- Uniform residual minimality: once an unsatisfiable specification exists,
a residual vocabulary supports Strong Totality for every specification exactly
when that vocabulary is inhabited. -/
theorem strongTotality_master_uniformResidualMinimality
    (S0 : Specification.{u})
    (hS0 : Not (Specification.Satisfiable S0))
    (E : Type r) :
    Nonempty E ↔
      forall S : Specification.{u}, Nonempty (ResolutionAnswerWith S E) :=
  residual_inhabited_iff_uniformStrongTotality S0 hS0 E

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

/-- Categorical canonicity: every pointed completion satisfying the universal
Strong Totality property is uniquely isomorphic, through solution- and
residual-preserving morphisms, to the canonical completion. -/
theorem strongTotality_master_uniqueCompletionIso
    (S : Specification.{u})
    (A : CompletionObject S)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual) :
    Exists fun i : CompletionIso A (canonicalCompletion S) =>
      forall j : CompletionIso A (canonicalCompletion S), j = i :=
  universalCompletion_unique_iso S A hA

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

/-- Coherent canonicity and naturality: for any two universal pointed
completions and any validity-preserving translation `f`, the unique canonical
isomorphisms and the unique map over `f` exist simultaneously and necessarily
make the canonical naturality square commute. -/
theorem strongTotality_master_canonicalNatural
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (A : CompletionObject S)
    (B : CompletionObject T)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual)
    (hB : IsUniversalTotalization T B.Carrier B.includeSolution B.residual) :
    Exists fun iS : CompletionIso A (canonicalCompletion S) =>
      (forall jS : CompletionIso A (canonicalCompletion S), jS = iS) ∧
      Exists fun iT : CompletionIso B (canonicalCompletion T) =>
        (forall jT : CompletionIso B (canonicalCompletion T), jT = iT) ∧
        Exists fun p : CompletionHomOver f A B =>
          (forall q : CompletionHomOver f A B, q = p) ∧
          CompletionHomOver.postcompVertical iT.hom p =
            CompletionHomOver.precompVertical
              (canonicalCompletionFunctorMap f) iS.hom :=
  universalCompletions_canonicalNatural f A B hA hB

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
