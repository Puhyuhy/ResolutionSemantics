import Std

universe u v w x

namespace Resolution
namespace Conditional

noncomputable local instance conditionalClassicalPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Initial models for many-sorted conditional equations

This module isolates the classical total-algebra result used in the proof of
Diaconescu's Corollary 4.2.  The construction is semantic: ground terms are
identified exactly when every model of the conditional theory gives them the
same value.  The resulting quotient is itself a model and is initial among
models of the theory.
-/

set_option linter.checkUnivs false in
structure Signature where
  SortId : Type u
  Op : Type u
  arity : Op -> Nat
  argSort : forall op : Op, Fin (arity op) -> SortId
  resultSort : Op -> SortId

abbrev Args
    (Sigma : Signature.{u})
    (A : Sigma.SortId -> Type v)
    (op : Sigma.Op) : Type v :=
  forall i : Fin (Sigma.arity op), A (Sigma.argSort op i)

inductive Term
    (Sigma : Signature.{u})
    (Var : Sigma.SortId -> Type x) : Sigma.SortId -> Type (max u x) where
  | var {s : Sigma.SortId} (name : Var s) : Term Sigma Var s
  | app (op : Sigma.Op)
      (args : forall i : Fin (Sigma.arity op),
        Term Sigma Var (Sigma.argSort op i)) :
      Term Sigma Var (Sigma.resultSort op)

structure Alg (Sigma : Signature.{u}) where
  Carrier : Sigma.SortId -> Type v
  eval : forall op : Sigma.Op, Args Sigma Carrier op ->
    Carrier (Sigma.resultSort op)

abbrev Assignment
    (Sigma : Signature.{u})
    (Var : Sigma.SortId -> Type x)
    (A : Sigma.SortId -> Type v) : Type (max u x v) :=
  forall s : Sigma.SortId, Var s -> A s

def Term.eval
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (A : Alg.{u,v} Sigma)
    (rho : Assignment Sigma Var A.Carrier) :
    {s : Sigma.SortId} -> Term Sigma Var s -> A.Carrier s
  | _, .var name => rho _ name
  | _, .app op args => A.eval op (fun i => (args i).eval A rho)

structure Hom
    {Sigma : Signature.{u}}
    (A : Alg.{u,v} Sigma)
    (B : Alg.{u,w} Sigma) where
  toFun : forall s : Sigma.SortId, A.Carrier s -> B.Carrier s
  map_op : forall (op : Sigma.Op) (args : Args Sigma A.Carrier op),
    toFun _ (A.eval op args) =
      B.eval op (fun i => toFun _ (args i))

namespace Hom

@[ext] theorem ext
    {Sigma : Signature.{u}}
    {A : Alg.{u,v} Sigma}
    {B : Alg.{u,w} Sigma}
    {f g : Hom A B}
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem map_term
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    {A : Alg.{u,v} Sigma}
    {B : Alg.{u,w} Sigma}
    (hom : Hom A B)
    (rho : Assignment Sigma Var A.Carrier)
    {sort : Sigma.SortId}
    (term : Term Sigma Var sort) :
    hom.toFun sort (term.eval A rho) =
      term.eval B (fun target name => hom.toFun target (rho target name)) := by
  induction term with
  | var name => rfl
  | app op args ih =>
      calc
        hom.toFun _ (A.eval op (fun i => (args i).eval A rho)) =
            B.eval op (fun i => hom.toFun _ ((args i).eval A rho)) :=
          hom.map_op op (fun i => (args i).eval A rho)
        _ = B.eval op (fun i =>
            (args i).eval B
              (fun target name => hom.toFun target (rho target name))) :=
          congrArg (B.eval op) (funext ih)

end Hom

inductive ContextVar
    (SortId : Type u) : List SortId -> SortId -> Type u where
  | here {s : SortId} {context : List SortId} :
      ContextVar SortId (s :: context) s
  | there {s t : SortId} {context : List SortId}
      (name : ContextVar SortId context s) :
      ContextVar SortId (t :: context) s

abbrev ContextAssignment
    (Sigma : Signature.{u})
    (A : Sigma.SortId -> Type v)
    (context : List Sigma.SortId) :=
  Assignment Sigma (ContextVar Sigma.SortId context) A

structure Equation
    (Sigma : Signature.{u})
    (Var : Sigma.SortId -> Type u) where
  sort : Sigma.SortId
  left : Term Sigma Var sort
  right : Term Sigma Var sort

def Equation.Sat
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type u}
    (equation : Equation Sigma Var)
    (A : Alg.{u,v} Sigma)
    (rho : Assignment Sigma Var A.Carrier) : Prop :=
  equation.left.eval A rho = equation.right.eval A rho

structure Clause (Sigma : Signature.{u}) where
  Var : Sigma.SortId -> Type u
  premises : List (Equation Sigma Var)
  conclusion : Equation Sigma Var

def Clause.Sat
    {Sigma : Signature.{u}}
    (clause : Clause Sigma)
    (A : Alg.{u,v} Sigma) : Prop :=
  forall rho : Assignment Sigma clause.Var A.Carrier,
    (forall premise, premise ∈ clause.premises -> premise.Sat A rho) ->
      clause.conclusion.Sat A rho

abbrev Theory (Sigma : Signature.{u}) := Clause Sigma -> Prop

def Models
    {Sigma : Signature.{u}}
    (A : Alg.{u,v} Sigma)
    (theory : Theory Sigma) : Prop :=
  forall clause, theory clause -> clause.Sat A

abbrev GroundTerm
    (Sigma : Signature.{u})
    (s : Sigma.SortId) :=
  Term Sigma (fun _ => Empty) s

def emptyAssignment
    {Sigma : Signature.{u}}
    (A : Sigma.SortId -> Type v) :
    Assignment Sigma (fun _ => Empty) A :=
  fun _ name => nomatch name

def GroundTerm.eval
    {Sigma : Signature.{u}}
    (A : Alg.{u,v} Sigma)
    {s : Sigma.SortId}
    (term : GroundTerm Sigma s) : A.Carrier s :=
  Term.eval A (emptyAssignment A.Carrier) term

def GroundEquivalent
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    {s : Sigma.SortId}
    (left right : GroundTerm Sigma s) : Prop :=
  forall (A : Alg.{u,v} Sigma), Models A theory ->
    left.eval A = right.eval A

theorem GroundEquivalent.refl
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    {s : Sigma.SortId}
    (term : GroundTerm Sigma s) :
    GroundEquivalent.{u,v} theory term term := by
  intro A hA
  rfl

theorem GroundEquivalent.symm
    {Sigma : Signature.{u}}
    {theory : Theory Sigma}
    {s : Sigma.SortId}
    {left right : GroundTerm Sigma s}
    (h : GroundEquivalent.{u,v} theory left right) :
    GroundEquivalent.{u,v} theory right left := by
  intro A hA
  exact (h A hA).symm

theorem GroundEquivalent.trans
    {Sigma : Signature.{u}}
    {theory : Theory Sigma}
    {s : Sigma.SortId}
    {left middle right : GroundTerm Sigma s}
    (hLeft : GroundEquivalent.{u,v} theory left middle)
    (hRight : GroundEquivalent.{u,v} theory middle right) :
    GroundEquivalent.{u,v} theory left right := by
  intro A hA
  exact (hLeft A hA).trans (hRight A hA)

def groundSetoid
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (s : Sigma.SortId) : Setoid (GroundTerm Sigma s) where
  r := GroundEquivalent.{u,v} theory
  iseqv :=
    { refl := GroundEquivalent.refl theory
      symm := GroundEquivalent.symm
      trans := GroundEquivalent.trans }

abbrev TermModelCarrier
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (s : Sigma.SortId) :=
  Quotient (groundSetoid.{u,v} theory s)

noncomputable def representative
    {alpha : Type u}
    {setoid : Setoid alpha}
    (value : Quotient setoid) : alpha :=
  Classical.choose (Quotient.exists_rep value)

@[simp] theorem representative_mk
    {alpha : Type u}
    {setoid : Setoid alpha}
    (value : Quotient setoid) :
    Quotient.mk setoid (representative value) = value :=
  Classical.choose_spec (Quotient.exists_rep value)

noncomputable def termModel
    {Sigma : Signature.{u}}
    (theory : Theory Sigma) : Alg.{u,u} Sigma where
  Carrier := TermModelCarrier.{u,v} theory
  eval := fun op args =>
    Quotient.mk _ (Term.app op (fun i => representative (args i)))

def Term.groundSubstitute
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (substitution : forall s : Sigma.SortId, Var s -> GroundTerm Sigma s) :
    {s : Sigma.SortId} -> Term Sigma Var s -> GroundTerm Sigma s
  | _, .var name => substitution _ name
  | _, .app op args =>
      .app op (fun i => (args i).groundSubstitute substitution)

theorem Term.groundSubstitute_eval
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (substitution : forall s : Sigma.SortId, Var s -> GroundTerm Sigma s)
    (A : Alg.{u,v} Sigma)
    {s : Sigma.SortId}
    (term : Term Sigma Var s) :
    (term.groundSubstitute substitution).eval A =
      term.eval A (fun t name => (substitution t name).eval A) := by
  induction term with
  | var name => rfl
  | app op args ih =>
      change A.eval op
          (fun i => (Term.groundSubstitute substitution (args i)).eval A) =
        A.eval op (fun i => Term.eval A
          (fun t name => (substitution t name).eval A) (args i))
      exact congrArg (A.eval op) (funext ih)

theorem GroundEquivalent.app
    {Sigma : Signature.{u}}
    {theory : Theory Sigma}
    (op : Sigma.Op)
    (left right : forall i : Fin (Sigma.arity op),
      GroundTerm Sigma (Sigma.argSort op i))
    (h : forall i, GroundEquivalent.{u,v} theory (left i) (right i)) :
    GroundEquivalent.{u,v} theory (Term.app op left) (Term.app op right) := by
  intro A hA
  change A.eval op (fun i => (left i).eval A) =
    A.eval op (fun i => (right i).eval A)
  exact congrArg (A.eval op) (funext (fun i => h i A hA))

noncomputable def termModelSubstitution
    {Sigma : Signature.{u}}
    {theory : Theory Sigma}
    {Var : Sigma.SortId -> Type u}
    (rho : Assignment Sigma Var (termModel.{u,v} theory).Carrier) :
    forall s : Sigma.SortId,
      Var s -> GroundTerm Sigma s :=
  fun _ name => representative (rho _ name)

theorem Term.eval_termModel_eq_mk_substitute
    {Sigma : Signature.{u}}
    {theory : Theory Sigma}
    {Var : Sigma.SortId -> Type u}
    (rho : Assignment Sigma Var (termModel.{u,v} theory).Carrier)
    {s : Sigma.SortId}
    (term : Term Sigma Var s) :
    term.eval (termModel.{u,v} theory) rho =
      Quotient.mk (groundSetoid.{u,v} theory s)
        (term.groundSubstitute (termModelSubstitution rho)) := by
  induction term with
  | var name =>
      exact (representative_mk (rho _ name)).symm
  | app op args ih =>
      change
        Quotient.mk (groundSetoid.{u,v} theory _)
            (Term.app op (fun i => representative
              (Term.eval (termModel.{u,v} theory) rho (args i)))) =
          Quotient.mk (groundSetoid.{u,v} theory _)
            (Term.app op (fun i =>
              Term.groundSubstitute (termModelSubstitution rho) (args i)))
      apply Quotient.sound
      apply GroundEquivalent.app
      intro i
      change (groundSetoid.{u,v} theory _).r
        (representative (Term.eval (termModel.{u,v} theory) rho (args i)))
        (Term.groundSubstitute (termModelSubstitution rho) (args i))
      exact Quotient.exact ((representative_mk
        (Term.eval (termModel.{u,v} theory) rho (args i))).trans (ih i))

theorem termModel_models
    {Sigma : Signature.{u}}
    (theory : Theory Sigma) :
    Models (termModel.{u,v} theory) theory := by
  intro clause hClause rho hPremises
  let substitution := termModelSubstitution (theory := theory) rho
  have hSemanticPremises : forall premise,
      premise ∈ clause.premises ->
      forall (A : Alg.{u,v} Sigma), Models A theory ->
        (premise.left.groundSubstitute substitution).eval A =
          (premise.right.groundSubstitute substitution).eval A := by
    intro premise hPremise A hA
    have hSat := hPremises premise hPremise
    have hLeft := premise.left.eval_termModel_eq_mk_substitute
      (theory := theory) rho
    have hRight := premise.right.eval_termModel_eq_mk_substitute
      (theory := theory) rho
    have hQuotient :
        Quotient.mk (groundSetoid.{u,v} theory premise.sort)
            (premise.left.groundSubstitute substitution) =
          Quotient.mk (groundSetoid.{u,v} theory premise.sort)
            (premise.right.groundSubstitute substitution) := by
      exact hLeft.symm.trans (hSat.trans hRight)
    exact (Quotient.exact hQuotient) A hA
  have hConclusionInModel : forall (A : Alg.{u,v} Sigma), Models A theory ->
      (clause.conclusion.left.groundSubstitute substitution).eval A =
        (clause.conclusion.right.groundSubstitute substitution).eval A := by
    intro A hA
    have hInstance := hA clause hClause
      (fun s name => (substitution s name).eval A)
    have hResult := hInstance (by
      intro premise hPremise
      change premise.left.eval A
          (fun s name => (substitution s name).eval A) =
        premise.right.eval A
          (fun s name => (substitution s name).eval A)
      rw [<- premise.left.groundSubstitute_eval substitution A,
        <- premise.right.groundSubstitute_eval substitution A]
      exact hSemanticPremises premise hPremise A hA)
    change clause.conclusion.left.eval A
        (fun s name => (substitution s name).eval A) =
      clause.conclusion.right.eval A
        (fun s name => (substitution s name).eval A) at hResult
    calc
      (clause.conclusion.left.groundSubstitute substitution).eval A =
          clause.conclusion.left.eval A
            (fun s name => (substitution s name).eval A) :=
        clause.conclusion.left.groundSubstitute_eval substitution A
      _ = clause.conclusion.right.eval A
            (fun s name => (substitution s name).eval A) := hResult
      _ = (clause.conclusion.right.groundSubstitute substitution).eval A :=
        (clause.conclusion.right.groundSubstitute_eval substitution A).symm
  have hLeft := clause.conclusion.left.eval_termModel_eq_mk_substitute
    (theory := theory) rho
  have hRight := clause.conclusion.right.eval_termModel_eq_mk_substitute
    (theory := theory) rho
  change clause.conclusion.left.eval (termModel.{u,v} theory) rho =
    clause.conclusion.right.eval (termModel.{u,v} theory) rho
  rw [hLeft, hRight]
  apply Quotient.sound
  exact hConclusionInModel

noncomputable def termModelHom
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (A : Alg.{u,v} Sigma)
    (hA : Models A theory) : Hom (termModel.{u,v} theory) A where
  toFun := fun _ value =>
    Quotient.lift (fun term => term.eval A)
      (by
        intro left right hEquivalent
        change GroundEquivalent.{u,v} theory left right at hEquivalent
        exact hEquivalent A hA) value
  map_op := by
    intro op args
    change
      GroundTerm.eval A (Term.app op (fun i => representative (args i))) =
        A.eval op (fun i => Quotient.lift
          (fun term => GroundTerm.eval A term)
          (by
            intro left right hEquivalent
            change GroundEquivalent.{u,v} theory left right at hEquivalent
            exact hEquivalent A hA) (args i))
    change A.eval op (fun i => GroundTerm.eval A (representative (args i))) =
      A.eval op (fun i => Quotient.lift
        (fun term => GroundTerm.eval A term)
        (by
          intro left right hEquivalent
          change GroundEquivalent.{u,v} theory left right at hEquivalent
          exact hEquivalent A hA) (args i))
    apply congrArg (A.eval op)
    funext i
    have hRepresentative := representative_mk (args i)
    exact congrArg
      (Quotient.lift (fun term => GroundTerm.eval A term)
        (by
          intro left right hEquivalent
          change GroundEquivalent.{u,v} theory left right at hEquivalent
          exact hEquivalent A hA)) hRepresentative

@[simp] theorem termModelHom_mk
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (A : Alg.{u,v} Sigma)
    (hA : Models A theory)
    {s : Sigma.SortId}
    (term : GroundTerm Sigma s) :
    (termModelHom theory A hA).toFun s
        (Quotient.mk (groundSetoid.{u,v} theory s) term) =
      term.eval A := rfl

theorem termModel_eval_mk
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (op : Sigma.Op)
    (args : forall i : Fin (Sigma.arity op),
      GroundTerm Sigma (Sigma.argSort op i)) :
    (termModel.{u,v} theory).eval op
        (fun i => Quotient.mk
          (groundSetoid.{u,v} theory (Sigma.argSort op i)) (args i)) =
      Quotient.mk (groundSetoid.{u,v} theory (Sigma.resultSort op))
        (Term.app op args) := by
  change
    Quotient.mk (groundSetoid.{u,v} theory _)
        (Term.app op (fun i => representative
          (Quotient.mk (groundSetoid.{u,v} theory _) (args i)))) =
      Quotient.mk (groundSetoid.{u,v} theory _) (Term.app op args)
  apply Quotient.sound
  apply GroundEquivalent.app
  intro i
  change (groundSetoid.{u,v} theory _).r
    (representative
      (Quotient.mk (groundSetoid.{u,v} theory _) (args i))) (args i)
  exact Quotient.exact (representative_mk
    (Quotient.mk (groundSetoid.{u,v} theory _) (args i)))

theorem termModelHom_unique
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (A : Alg.{u,v} Sigma)
    (hA : Models A theory)
    (candidate : Hom (termModel.{u,v} theory) A) :
    candidate = termModelHom theory A hA := by
  apply Hom.ext
  funext s value
  refine Quotient.inductionOn value ?_
  intro term
  change candidate.toFun s
      (Quotient.mk (groundSetoid.{u,v} theory s) term) = term.eval A
  induction term with
  | var name => exact nomatch name
  | app op args ih =>
      calc
        candidate.toFun _
            (Quotient.mk (groundSetoid.{u,v} theory _) (Term.app op args)) =
            candidate.toFun _ ((termModel.{u,v} theory).eval op
              (fun i => Quotient.mk
                (groundSetoid.{u,v} theory _) (args i))) :=
          congrArg (candidate.toFun _)
            (termModel_eval_mk theory op args).symm
        _ = A.eval op (fun i => candidate.toFun _
              (Quotient.mk (groundSetoid.{u,v} theory _) (args i))) :=
          candidate.map_op op (fun i =>
            Quotient.mk (groundSetoid.{u,v} theory _) (args i))
        _ = A.eval op (fun i => GroundTerm.eval A (args i)) :=
          congrArg (A.eval op) (funext (fun i => ih i
            (Quotient.mk (groundSetoid.{u,v} theory _) (args i))))
        _ = GroundTerm.eval A (Term.app op args) := rfl

structure IsInitialModel
    {Sigma : Signature.{u}}
    (theory : Theory Sigma)
    (A : Alg.{u,u} Sigma) : Prop where
  models : Models A theory
  hom_unique : forall B : Alg.{u,v} Sigma, Models B theory ->
    Exists fun initialMap : Hom A B =>
      forall candidate : Hom A B, candidate = initialMap

theorem termModel_initial
    {Sigma : Signature.{u}}
    (theory : Theory Sigma) :
    IsInitialModel.{u,v} theory (termModel.{u,v} theory) where
  models := termModel_models theory
  hom_unique := by
    intro A hA
    exact ⟨termModelHom theory A hA,
      termModelHom_unique theory A hA⟩

theorem initial_model_exists
    {Sigma : Signature.{u}}
    (theory : Theory Sigma) :
    Exists fun A : Alg.{u,u} Sigma => IsInitialModel.{u,v} theory A :=
  ⟨termModel.{u,v} theory, termModel_initial theory⟩

end Conditional
end Resolution
