import ResolutionConditionalInitial
import ResolutionDiaconescuAdjunction

universe u v w

namespace Resolution
namespace Diaconescu
namespace InitialExistence

open ManySorted
open Resolution.Conditional

noncomputable local instance initialExistenceClassicalPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Conditional-equational existence layer for the Diaconescu bridge

This module connects the generic initial-model construction for many-sorted
conditional equations with the total signature underlying the encoding.  It
is intentionally separate from the adjunction module: the latter proves the
categorical transfer, while this file supplies the classical existence input.
-/

inductive EncodedSort (Sigma : ManySorted.Signature.{u}) : Type u where
  | data (sort : Sigma.SortId)
  | truth

inductive EncodedOp (Sigma : ManySorted.Signature.{u}) : Type u where
  | total (op : Sigma.TotalOp)
  | partialSymbol (op : Sigma.PartialOp)
  | existenceEq (sort : Sigma.SortId)
  | trueValue

abbrev encodedTotalSignature
    (Sigma : ManySorted.Signature.{u}) : Conditional.Signature.{u} where
  SortId := EncodedSort Sigma
  Op := EncodedOp Sigma
  arity
    | .total op => Sigma.totalArity op
    | .partialSymbol op => Sigma.partialArity op
    | .existenceEq _ => 2
    | .trueValue => 0
  argSort
    | .total op, i => .data (Sigma.totalArgSort op i)
    | .partialSymbol op, i => .data (Sigma.partialArgSort op i)
    | .existenceEq sort, _ => .data sort
    | .trueValue, i => nomatch i
  resultSort
    | .total op => .data (Sigma.totalResultSort op)
    | .partialSymbol op => .data (Sigma.partialResultSort op)
    | .existenceEq _ => .truth
    | .trueValue => .truth

abbrev EncodedAlg.toConditional
    {Sigma : ManySorted.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma) :
    Conditional.Alg.{u,v} (encodedTotalSignature Sigma) where
  Carrier
    | .data sort => M.Data sort
    | .truth => M.Truth
  eval
    | .total op, args => M.evalTotal op args
    | .partialSymbol op, args => M.evalPartialSymbol op args
    | .existenceEq sort, args =>
        M.existenceEq sort (args 0) (args 1)
    | .trueValue, _ => M.trueValue

abbrev conditionalToEncodedAlg
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)) :
    ManySorted.EncodedAlg.{u,v,v} Sigma where
  Data sort := A.Carrier (.data sort)
  Truth := A.Carrier .truth
  evalTotal op args := A.eval (.total op) args
  evalPartialSymbol op args := A.eval (.partialSymbol op) args
  existenceEq sort left right :=
    A.eval (.existenceEq sort) (Fin.cases left (fun _ => right))
  trueValue := A.eval .trueValue (fun i => nomatch i)

def EncodedHom.toConditional
    {Sigma : ManySorted.Signature.{u}}
    {M : ManySorted.EncodedAlg.{u,v,v} Sigma}
    {N : ManySorted.EncodedAlg.{u,w,w} Sigma}
    (hom : ManySorted.EncodedHom M N) :
    Conditional.Hom (EncodedAlg.toConditional M)
      (EncodedAlg.toConditional N) where
  toFun
    | .data sort => hom.dataMap sort
    | .truth => hom.truthMap
  map_op := by
    intro op args
    cases op with
    | total op => exact hom.map_total op args
    | partialSymbol op => exact hom.map_partial_symbol op args
    | existenceEq sort =>
        exact hom.map_existenceEq sort (args 0) (args 1)
    | trueValue => exact hom.map_true

def conditionalHomToEncoded
    {Sigma : ManySorted.Signature.{u}}
    {A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)}
    {B : Conditional.Alg.{u,w} (encodedTotalSignature Sigma)}
    (hom : Conditional.Hom A B) :
    ManySorted.EncodedHom (conditionalToEncodedAlg A)
      (conditionalToEncodedAlg B) where
  dataMap sort := hom.toFun (.data sort)
  truthMap := hom.toFun .truth
  map_total op args := hom.map_op (.total op) args
  map_partial_symbol op args := hom.map_op (.partialSymbol op) args
  map_existenceEq sort left right := by
    change hom.toFun .truth
        (A.eval (.existenceEq sort) (Fin.cases left (fun _ => right))) =
      B.eval (.existenceEq sort)
        (Fin.cases (hom.toFun (.data sort) left)
          (fun _ => hom.toFun (.data sort) right))
    calc
      _ = B.eval (.existenceEq sort)
          (fun i => hom.toFun (.data sort)
            (Fin.cases left (fun _ => right) i)) :=
        hom.map_op (.existenceEq sort) (Fin.cases left (fun _ => right))
      _ = B.eval (.existenceEq sort)
          (Fin.cases (hom.toFun (.data sort) left)
            (fun _ => hom.toFun (.data sort) right)) := by
        apply congrArg (B.eval (.existenceEq sort))
        funext i
        refine Fin.cases rfl ?_ i
        intro j
        rfl
  map_true := by
    change hom.toFun .truth (A.eval .trueValue (fun i => nomatch i)) =
      B.eval .trueValue (fun i => nomatch i)
    calc
      _ = B.eval .trueValue
          (fun i => hom.toFun (nomatch i) (nomatch i)) :=
        hom.map_op .trueValue (fun i => nomatch i)
      _ = B.eval .trueValue (fun i => nomatch i) := by
        apply congrArg (B.eval .trueValue)
        funext i
        exact Fin.elim0 i

/-! ## The conditional clauses `Gamma` -/

def LiftDataVar
    {Sigma : ManySorted.Signature.{u}}
    (Var : Sigma.SortId -> Type u) : EncodedSort Sigma -> Type u
  | .data sort => Var sort
  | .truth => ULift.{u,0} PEmpty

def encodeDataTerm
    {Sigma : ManySorted.Signature.{u}}
    {Var : Sigma.SortId -> Type u}
    {sort : Sigma.SortId} :
    ManySorted.Term Sigma Var sort ->
      Conditional.Term (encodedTotalSignature Sigma) (LiftDataVar Var)
        (.data sort)
  | .var name => .var name
  | .total op args =>
      Conditional.Term.app
        (Sigma := encodedTotalSignature Sigma)
        (Var := LiftDataVar Var)
        (EncodedOp.total op) (fun i => encodeDataTerm (args i))
  | .partialApp op args =>
      Conditional.Term.app
        (Sigma := encodedTotalSignature Sigma)
        (Var := LiftDataVar Var)
        (EncodedOp.partialSymbol op) (fun i => encodeDataTerm (args i))

def indexedDataVar
    {Sigma : ManySorted.Signature.{u}}
    {n : Nat}
    (sortAt : Fin n -> Sigma.SortId) : EncodedSort Sigma -> Type u
  | .data sort => ULift.{u,0} {i : Fin n // sortAt i = sort}
  | .truth => ULift.{u,0} PEmpty

def indexedDataTerm
    {Sigma : ManySorted.Signature.{u}}
    {n : Nat}
    (sortAt : Fin n -> Sigma.SortId)
    (i : Fin n) :
    Conditional.Term (encodedTotalSignature Sigma) (indexedDataVar sortAt)
      (.data (sortAt i)) :=
  .var (ULift.up ⟨i, rfl⟩)

def indexedVarName
    {Sigma : ManySorted.Signature.{u}}
    {n : Nat}
    (sortAt : Fin n -> Sigma.SortId)
    (i : Fin n) : indexedDataVar sortAt (.data (sortAt i)) :=
  ULift.up ⟨i, rfl⟩

def encodedExistenceTerm
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (sort : Sigma.SortId)
    (left right : Conditional.Term (encodedTotalSignature Sigma) Var
      (.data sort)) :
    Conditional.Term (encodedTotalSignature Sigma) Var .truth :=
  Conditional.Term.app
    (Sigma := encodedTotalSignature Sigma)
    (Var := Var)
    (EncodedOp.existenceEq sort) (Fin.cases left (fun _ => right))

def encodedTrueTerm
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u} :
    Conditional.Term (encodedTotalSignature Sigma) Var .truth :=
  Conditional.Term.app
    (Sigma := encodedTotalSignature Sigma)
    (Var := Var)
    EncodedOp.trueValue (fun i => nomatch i)

def dataEquation
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    {sort : Sigma.SortId}
    (left right : Conditional.Term (encodedTotalSignature Sigma) Var
      (.data sort)) :
    Conditional.Equation (encodedTotalSignature Sigma) Var where
  sort := .data sort
  left := left
  right := right

def truthEquation
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (left right : Conditional.Term (encodedTotalSignature Sigma) Var .truth) :
    Conditional.Equation (encodedTotalSignature Sigma) Var where
  sort := .truth
  left := left
  right := right

def definedEquation
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    {sort : Sigma.SortId}
    (term : Conditional.Term (encodedTotalSignature Sigma) Var (.data sort)) :
    Conditional.Equation (encodedTotalSignature Sigma) Var :=
  truthEquation (encodedExistenceTerm sort term term) encodedTrueTerm

def totalArgumentSorts
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.TotalOp) : Fin (Sigma.totalArity op) -> Sigma.SortId :=
  Sigma.totalArgSort op

def partialArgumentSorts
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.PartialOp) : Fin (Sigma.partialArity op) -> Sigma.SortId :=
  Sigma.partialArgSort op

def totalApplicationTerm
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.TotalOp) :
    Conditional.Term (encodedTotalSignature Sigma)
      (indexedDataVar (totalArgumentSorts op))
      (.data (Sigma.totalResultSort op)) :=
  Conditional.Term.app
    (Sigma := encodedTotalSignature Sigma)
    (Var := indexedDataVar (totalArgumentSorts op))
    (EncodedOp.total op)
    (fun i => indexedDataTerm (totalArgumentSorts op) i)

def partialApplicationTerm
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.PartialOp) :
    Conditional.Term (encodedTotalSignature Sigma)
      (indexedDataVar (partialArgumentSorts op))
      (.data (Sigma.partialResultSort op)) :=
  Conditional.Term.app
    (Sigma := encodedTotalSignature Sigma)
    (Var := indexedDataVar (partialArgumentSorts op))
    (EncodedOp.partialSymbol op)
    (fun i => indexedDataTerm (partialArgumentSorts op) i)

abbrev gammaTotalPreservesClause
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.TotalOp) :
    Conditional.Clause (encodedTotalSignature Sigma) where
  Var := indexedDataVar (totalArgumentSorts op)
  premises := List.ofFn (fun i =>
    definedEquation (indexedDataTerm (totalArgumentSorts op) i))
  conclusion := definedEquation (totalApplicationTerm op)

abbrev gammaEqualityDefinedClause
    {Sigma : ManySorted.Signature.{u}}
    (sort : Sigma.SortId) :
    Conditional.Clause (encodedTotalSignature Sigma) :=
  let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
  let left := indexedDataTerm sortAt (0 : Fin 2)
  let right := indexedDataTerm sortAt (1 : Fin 2)
  { Var := indexedDataVar sortAt
    premises := [truthEquation
      (encodedExistenceTerm sort left right) encodedTrueTerm]
    conclusion := definedEquation left }

abbrev gammaEqualitySoundClause
    {Sigma : ManySorted.Signature.{u}}
    (sort : Sigma.SortId) :
    Conditional.Clause (encodedTotalSignature Sigma) :=
  let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
  let left := indexedDataTerm sortAt (0 : Fin 2)
  let right := indexedDataTerm sortAt (1 : Fin 2)
  { Var := indexedDataVar sortAt
    premises := [truthEquation
      (encodedExistenceTerm sort left right) encodedTrueTerm]
    conclusion := dataEquation left right }

abbrev gammaTotalReflectsClause
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.TotalOp)
    (i : Fin (Sigma.totalArity op)) :
    Conditional.Clause (encodedTotalSignature Sigma) where
  Var := indexedDataVar (totalArgumentSorts op)
  premises := [definedEquation (totalApplicationTerm op)]
  conclusion := definedEquation
    (indexedDataTerm (totalArgumentSorts op) i)

abbrev gammaPartialReflectsClause
    {Sigma : ManySorted.Signature.{u}}
    (op : Sigma.PartialOp)
    (i : Fin (Sigma.partialArity op)) :
    Conditional.Clause (encodedTotalSignature Sigma) where
  Var := indexedDataVar (partialArgumentSorts op)
  premises := [definedEquation (partialApplicationTerm op)]
  conclusion := definedEquation
    (indexedDataTerm (partialArgumentSorts op) i)

inductive IsGammaClause
    {Sigma : ManySorted.Signature.{u}} :
    Conditional.Clause (encodedTotalSignature Sigma) -> Prop where
  | totalPreserves (op : Sigma.TotalOp) :
      IsGammaClause (gammaTotalPreservesClause op)
  | equalityDefined (sort : Sigma.SortId) :
      IsGammaClause (gammaEqualityDefinedClause sort)
  | equalitySound (sort : Sigma.SortId) :
      IsGammaClause (gammaEqualitySoundClause sort)
  | totalReflects (op : Sigma.TotalOp)
      (i : Fin (Sigma.totalArity op)) :
      IsGammaClause (gammaTotalReflectsClause op i)
  | partialReflects (op : Sigma.PartialOp)
      (i : Fin (Sigma.partialArity op)) :
      IsGammaClause (gammaPartialReflectsClause op i)

abbrev gammaConditionalTheory
    (Sigma : ManySorted.Signature.{u}) :
    Conditional.Theory (encodedTotalSignature Sigma) :=
  IsGammaClause

theorem modelsGamma_of_satisfiesGamma
    {Sigma : ManySorted.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M) :
    Conditional.Models (EncodedAlg.toConditional M)
      (gammaConditionalTheory Sigma) := by
  intro clause hClause
  cases hClause with
  | totalPreserves op =>
      simp only [Conditional.Clause.Sat, gammaTotalPreservesClause]
      intro rho hPremises
      change M.existenceEq _
          (M.evalTotal op (fun i => rho _
            (indexedVarName (totalArgumentSorts op) i)))
          (M.evalTotal op (fun i => rho _
            (indexedVarName (totalArgumentSorts op) i))) = M.trueValue
      apply hM.total_preserves_defined
      intro i
      have hPremise := hPremises
        (definedEquation
          (indexedDataTerm (totalArgumentSorts op) i))
        (by
          rw [List.mem_ofFn]
          exact ⟨i, rfl⟩)
      change M.existenceEq _
          (rho _ (indexedVarName (totalArgumentSorts op) i))
          (rho _ (indexedVarName (totalArgumentSorts op) i)) =
        M.trueValue at hPremise
      exact hPremise
  | equalityDefined sort =>
      simp only [Conditional.Clause.Sat, gammaEqualityDefinedClause]
      intro rho hPremises
      let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
      let left := indexedDataTerm sortAt (0 : Fin 2)
      let right := indexedDataTerm sortAt (1 : Fin 2)
      have hPremise := hPremises
        (truthEquation
          (encodedExistenceTerm sort
            (indexedDataTerm (fun _ : Fin 2 => sort) (0 : Fin 2))
            (indexedDataTerm (fun _ : Fin 2 => sort) (1 : Fin 2)))
          encodedTrueTerm) (by simp)
      change M.existenceEq sort
          (rho _ (indexedVarName sortAt (0 : Fin 2)))
          (rho _ (indexedVarName sortAt (1 : Fin 2))) =
        M.trueValue at hPremise
      change M.existenceEq sort
          (rho _ (indexedVarName sortAt (0 : Fin 2)))
          (rho _ (indexedVarName sortAt (0 : Fin 2))) = M.trueValue
      exact hM.equality_defined_left sort _ _ hPremise
  | equalitySound sort =>
      simp only [Conditional.Clause.Sat, gammaEqualitySoundClause]
      intro rho hPremises
      let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
      let left := indexedDataTerm sortAt (0 : Fin 2)
      let right := indexedDataTerm sortAt (1 : Fin 2)
      have hPremise := hPremises
        (truthEquation
          (encodedExistenceTerm sort
            (indexedDataTerm (fun _ : Fin 2 => sort) (0 : Fin 2))
            (indexedDataTerm (fun _ : Fin 2 => sort) (1 : Fin 2)))
          encodedTrueTerm) (by simp)
      change M.existenceEq sort
          (rho _ (indexedVarName sortAt (0 : Fin 2)))
          (rho _ (indexedVarName sortAt (1 : Fin 2))) =
        M.trueValue at hPremise
      change rho _ (indexedVarName sortAt (0 : Fin 2)) =
        rho _ (indexedVarName sortAt (1 : Fin 2))
      exact hM.equality_sound sort _ _ hPremise
  | totalReflects op i =>
      simp only [Conditional.Clause.Sat, gammaTotalReflectsClause]
      intro rho hPremises
      have hPremise := hPremises
        (definedEquation (totalApplicationTerm op)) (by simp)
      change M.existenceEq _
          (M.evalTotal op (fun j => rho _
            (indexedVarName (totalArgumentSorts op) j)))
          (M.evalTotal op (fun j => rho _
            (indexedVarName (totalArgumentSorts op) j))) =
        M.trueValue at hPremise
      change M.existenceEq _
          (rho _ (indexedVarName (totalArgumentSorts op) i))
          (rho _ (indexedVarName (totalArgumentSorts op) i)) = M.trueValue
      exact hM.total_reflects_defined op
        (fun j => rho _ (indexedVarName (totalArgumentSorts op) j))
        hPremise i
  | partialReflects op i =>
      simp only [Conditional.Clause.Sat, gammaPartialReflectsClause]
      intro rho hPremises
      have hPremise := hPremises
        (definedEquation (partialApplicationTerm op)) (by simp)
      change M.existenceEq _
          (M.evalPartialSymbol op
            (fun j => rho _
              (indexedVarName (partialArgumentSorts op) j)))
          (M.evalPartialSymbol op
            (fun j => rho _
              (indexedVarName (partialArgumentSorts op) j))) =
        M.trueValue at hPremise
      change M.existenceEq _
          (rho _ (indexedVarName (partialArgumentSorts op) i))
          (rho _ (indexedVarName (partialArgumentSorts op) i)) = M.trueValue
      exact hM.partial_reflects_defined op
        (fun j => rho _ (indexedVarName (partialArgumentSorts op) j))
        hPremise i

def indexedAssignment
    {Sigma : ManySorted.Signature.{u}}
    {A : EncodedSort Sigma -> Type v}
    {n : Nat}
    (sortAt : Fin n -> Sigma.SortId)
    (args : forall i : Fin n, A (.data (sortAt i))) :
    Conditional.Assignment (encodedTotalSignature Sigma)
      (indexedDataVar sortAt) A
  | .data _sort, name =>
      cast (congrArg (fun target => A (.data target)) name.down.property)
        (args name.down.val)
  | .truth, name => nomatch name.down

@[simp] theorem indexedAssignment_var
    {Sigma : ManySorted.Signature.{u}}
    {A : EncodedSort Sigma -> Type v}
    {n : Nat}
    (sortAt : Fin n -> Sigma.SortId)
    (args : forall i : Fin n, A (.data (sortAt i)))
    (i : Fin n) :
    indexedAssignment sortAt args _ (indexedVarName sortAt i) = args i := rfl

theorem satisfiesGamma_of_modelsGamma
    {Sigma : ManySorted.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hModels : Conditional.Models (EncodedAlg.toConditional M)
      (gammaConditionalTheory Sigma)) :
    ManySorted.SatisfiesGamma M := by
  refine
    { total_preserves_defined := ?_
      equality_defined_left := ?_
      equality_sound := ?_
      total_reflects_defined := ?_
      partial_reflects_defined := ?_ }
  · intro op args hArgs
    let rho := indexedAssignment (A := (EncodedAlg.toConditional M).Carrier)
      (totalArgumentSorts op) args
    have hClause := hModels (gammaTotalPreservesClause op)
      (.totalPreserves op)
    have hResult := hClause rho (by
      intro premise hPremise
      rw [List.mem_ofFn] at hPremise
      rcases hPremise with ⟨i, rfl⟩
      change M.existenceEq _ (args i) (args i) = M.trueValue
      exact hArgs i)
    change M.existenceEq _ (M.evalTotal op args) (M.evalTotal op args) =
      M.trueValue at hResult
    exact hResult
  · intro sort left right hEquality
    let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
    let args : forall _ : Fin 2, M.Data sort :=
      Fin.cases left (fun _ => right)
    let rho := indexedAssignment (A := (EncodedAlg.toConditional M).Carrier)
      sortAt args
    have hClause := hModels (gammaEqualityDefinedClause sort)
      (.equalityDefined sort)
    have hResult := hClause rho (by
      intro premise hPremise
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hPremise
      subst premise
      change M.existenceEq sort left right = M.trueValue
      exact hEquality)
    change M.existenceEq sort left left = M.trueValue at hResult
    exact hResult
  · intro sort left right hEquality
    let sortAt : Fin 2 -> Sigma.SortId := fun _ => sort
    let args : forall _ : Fin 2, M.Data sort :=
      Fin.cases left (fun _ => right)
    let rho := indexedAssignment (A := (EncodedAlg.toConditional M).Carrier)
      sortAt args
    have hClause := hModels (gammaEqualitySoundClause sort)
      (.equalitySound sort)
    have hResult := hClause rho (by
      intro premise hPremise
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hPremise
      subst premise
      change M.existenceEq sort left right = M.trueValue
      exact hEquality)
    change left = right at hResult
    exact hResult
  · intro op args hDefined i
    let rho := indexedAssignment (A := (EncodedAlg.toConditional M).Carrier)
      (totalArgumentSorts op) args
    have hClause := hModels (gammaTotalReflectsClause op i)
      (.totalReflects op i)
    have hResult := hClause rho (by
      intro premise hPremise
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hPremise
      subst premise
      change M.existenceEq _ (M.evalTotal op args) (M.evalTotal op args) =
        M.trueValue
      exact hDefined)
    change M.existenceEq _ (args i) (args i) = M.trueValue at hResult
    exact hResult
  · intro op args hDefined i
    let rho := indexedAssignment (A := (EncodedAlg.toConditional M).Carrier)
      (partialArgumentSorts op) args
    have hClause := hModels (gammaPartialReflectsClause op i)
      (.partialReflects op i)
    have hResult := hClause rho (by
      intro premise hPremise
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hPremise
      subst premise
      change M.existenceEq _
          (M.evalPartialSymbol op args) (M.evalPartialSymbol op args) =
        M.trueValue
      exact hDefined)
    change M.existenceEq _ (args i) (args i) = M.trueValue at hResult
    exact hResult

theorem modelsGamma_iff_satisfiesGamma
    {Sigma : ManySorted.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma) :
    Conditional.Models (EncodedAlg.toConditional M)
        (gammaConditionalTheory Sigma) <->
      ManySorted.SatisfiesGamma M :=
  ⟨satisfiesGamma_of_modelsGamma M, modelsGamma_of_satisfiesGamma M⟩

/-! ## Quasi-existence equations and their conditional translation -/

structure ExistenceAtom
    (Sigma : ManySorted.Signature.{u})
    (context : List Sigma.SortId) where
  sort : Sigma.SortId
  left : ManySorted.Term Sigma
    (ManySorted.ContextVar Sigma.SortId context) sort
  right : ManySorted.Term Sigma
    (ManySorted.ContextVar Sigma.SortId context) sort

def ExistenceAtom.Sat
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (atom : ExistenceAtom Sigma context)
    (A : ManySorted.PartialAlg.{u,v} Sigma)
    (rho : ManySorted.ContextAssignment Sigma A.Carrier context) : Prop :=
  Exists fun value : A.Carrier atom.sort =>
    atom.left.evalPartial A rho = some value /\
      atom.right.evalPartial A rho = some value

def ExistenceAtom.toFormula
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (atom : ExistenceAtom Sigma context) :
    ManySorted.Formula Sigma context :=
  .existenceEquality atom.left atom.right

@[simp] theorem ExistenceAtom.toFormula_sat
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (atom : ExistenceAtom Sigma context)
    (A : ManySorted.PartialAlg.{u,v} Sigma)
    (rho : ManySorted.ContextAssignment Sigma A.Carrier context) :
    atom.toFormula.Sat A rho <-> atom.Sat A rho :=
  Iff.rfl

structure QuasiEquation (Sigma : ManySorted.Signature.{u}) where
  context : List Sigma.SortId
  premises : List (ExistenceAtom Sigma context)
  conclusion : ExistenceAtom Sigma context

def QuasiEquation.Sat
    {Sigma : ManySorted.Signature.{u}}
    (equation : QuasiEquation Sigma)
    (A : ManySorted.PartialAlg.{u,v} Sigma) : Prop :=
  forall rho : ManySorted.ContextAssignment Sigma A.Carrier equation.context,
    (forall premise, premise ∈ equation.premises -> premise.Sat A rho) ->
      equation.conclusion.Sat A rho

def hornFormula
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId} :
    List (ExistenceAtom Sigma context) ->
      ExistenceAtom Sigma context -> ManySorted.Formula Sigma context
  | [], conclusion => conclusion.toFormula
  | premise :: rest, conclusion =>
      .negation (.conjunction premise.toFormula
        (.negation (hornFormula rest conclusion)))

theorem hornFormula_sat_iff
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (premises : List (ExistenceAtom Sigma context))
    (conclusion : ExistenceAtom Sigma context)
    (A : ManySorted.PartialAlg.{u,v} Sigma)
    (rho : ManySorted.ContextAssignment Sigma A.Carrier context) :
    (hornFormula premises conclusion).Sat A rho <->
      ((forall premise, premise ∈ premises -> premise.Sat A rho) ->
        conclusion.Sat A rho) := by
  induction premises with
  | nil =>
      constructor
      · intro h _
        exact h
      · intro h
        exact h (by
          intro premise hPremise
          cases hPremise)
  | cons premise rest ih =>
      change
        (Not (premise.Sat A rho /\
          Not ((hornFormula rest conclusion).Sat A rho))) <->
        ((forall candidate, candidate ∈ premise :: rest ->
            candidate.Sat A rho) -> conclusion.Sat A rho)
      constructor
      · intro h hAll
        have hRestSat : (hornFormula rest conclusion).Sat A rho := by
          by_cases hRest : (hornFormula rest conclusion).Sat A rho
          · exact hRest
          · exact False.elim (h ⟨hAll premise (by simp), hRest⟩)
        exact (ih.mp hRestSat) (by
          intro candidate hCandidate
          exact hAll candidate (by simp [hCandidate]))
      · intro h hCounterexample
        rcases hCounterexample with ⟨hPremise, hNotRest⟩
        apply hNotRest
        apply ih.mpr
        intro hRest
        apply h
        intro candidate hCandidate
        simp only [List.mem_cons] at hCandidate
        rcases hCandidate with hCandidate | hCandidate
        · cases hCandidate
          exact hPremise
        · exact hRest candidate hCandidate

def closeFormula
    {Sigma : ManySorted.Signature.{u}} :
    {context : List Sigma.SortId} ->
      ManySorted.Formula Sigma context -> ManySorted.Formula Sigma []
  | [], formula => formula
  | sort :: _context, formula =>
      closeFormula (.universal sort formula)

def contextAssignmentTail
    {Sigma : ManySorted.Signature.{u}}
    {A : Sigma.SortId -> Type v}
    {sort : Sigma.SortId}
    {context : List Sigma.SortId}
    (rho : ManySorted.ContextAssignment Sigma A (sort :: context)) :
    ManySorted.ContextAssignment Sigma A context :=
  fun _ name => rho _ (.there name)

def contextAssignmentHead
    {Sigma : ManySorted.Signature.{u}}
    {A : Sigma.SortId -> Type v}
    {sort : Sigma.SortId}
    {context : List Sigma.SortId}
    (rho : ManySorted.ContextAssignment Sigma A (sort :: context)) : A sort :=
  rho sort .here

@[simp] theorem contextAssignment_extend_tail_head
    {Sigma : ManySorted.Signature.{u}}
    {A : Sigma.SortId -> Type v}
    {sort : Sigma.SortId}
    {context : List Sigma.SortId}
    (rho : ManySorted.ContextAssignment Sigma A (sort :: context)) :
    ManySorted.ContextAssignment.extend (contextAssignmentTail rho)
      (contextAssignmentHead rho) = rho := by
  funext target name
  cases name <;> rfl

theorem closeFormula_sat_iff
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (formula : ManySorted.Formula Sigma context)
    (A : ManySorted.PartialAlg.{u,v} Sigma) :
    (closeFormula formula).Holds A <->
      forall rho : ManySorted.ContextAssignment Sigma A.Carrier context,
        formula.Sat A rho := by
  induction context with
  | nil =>
      constructor
      · intro h rho
        have hRho : rho = ManySorted.emptyContextAssignment A.Carrier := by
          funext sort name
          cases name
        simpa [closeFormula, ManySorted.Formula.Holds, hRho]
          using h
      · intro h
        exact h (ManySorted.emptyContextAssignment A.Carrier)
  | cons sort context ih =>
      rw [closeFormula, ih]
      constructor
      · intro h rho
        have hAt := h (contextAssignmentTail rho)
          (contextAssignmentHead rho)
        simpa only [contextAssignment_extend_tail_head] using hAt
      · intro h rho value
        exact h (ManySorted.ContextAssignment.extend rho value)

def QuasiEquation.toFormula
    {Sigma : ManySorted.Signature.{u}}
    (equation : QuasiEquation Sigma) : ManySorted.Formula Sigma [] :=
  closeFormula (hornFormula equation.premises equation.conclusion)

theorem QuasiEquation.toFormula_holds_iff
    {Sigma : ManySorted.Signature.{u}}
    (equation : QuasiEquation Sigma)
    (A : ManySorted.PartialAlg.{u,v} Sigma) :
    equation.toFormula.Holds A <-> equation.Sat A := by
  rw [QuasiEquation.toFormula, closeFormula_sat_iff]
  constructor
  · intro h rho hPremises
    exact (hornFormula_sat_iff equation.premises equation.conclusion A rho).1
      (h rho) hPremises
  · intro h rho
    exact (hornFormula_sat_iff equation.premises equation.conclusion A rho).2
      (h rho)

abbrev QuasiTheory
    (Sigma : ManySorted.Signature.{u}) := QuasiEquation Sigma -> Prop

def QuasiTheory.toPartialTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) : ManySorted.PartialTheory Sigma :=
  fun formula => Exists fun equation =>
    theory equation /\ equation.toFormula = formula

theorem models_quasiTheory_iff
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma)
    (A : ManySorted.PartialAlg.{u,v} Sigma) :
    ManySorted.ModelsPartialTheory A theory.toPartialTheory <->
      forall equation, theory equation -> equation.Sat A := by
  constructor
  · intro hModels equation hEquation
    apply (equation.toFormula_holds_iff A).1
    exact hModels equation.toFormula ⟨equation, hEquation, rfl⟩
  · intro hModels formula hFormula
    rcases hFormula with ⟨equation, hEquation, rfl⟩
    exact (equation.toFormula_holds_iff A).2 (hModels equation hEquation)

abbrev ContextEntry
    {Sigma : ManySorted.Signature.{u}}
    (context : List Sigma.SortId) :=
  _root_.Sigma fun sort => ManySorted.ContextVar Sigma.SortId context sort

def liftContextEntry
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    {head : Sigma.SortId} :
    ContextEntry context -> ContextEntry (head :: context)
  | ⟨sort, name⟩ => ⟨sort, .there name⟩

def contextEntries
    {Sigma : ManySorted.Signature.{u}} :
    (context : List Sigma.SortId) -> List (ContextEntry context)
  | [] => []
  | head :: context =>
      ⟨head, .here⟩ :: (contextEntries context).map liftContextEntry

theorem contextEntry_mem
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    {sort : Sigma.SortId}
    (name : ManySorted.ContextVar Sigma.SortId context sort) :
    (⟨sort, name⟩ : ContextEntry context) ∈ contextEntries context := by
  induction name with
  | here =>
      exact List.mem_cons_self
  | there name ih =>
      apply List.mem_cons_of_mem
      exact List.mem_map_of_mem ih

def contextGuardEquation
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (entry : ContextEntry context) :
    Conditional.Equation (encodedTotalSignature Sigma)
      (LiftDataVar (ManySorted.ContextVar Sigma.SortId context)) :=
  match entry with
  | ⟨_sort, name⟩ =>
      definedEquation (encodeDataTerm (ManySorted.Term.var name))

def contextGuardEquations
    {Sigma : ManySorted.Signature.{u}}
    (context : List Sigma.SortId) :
    List (Conditional.Equation (encodedTotalSignature Sigma)
      (LiftDataVar (ManySorted.ContextVar Sigma.SortId context))) :=
  (contextEntries context).map contextGuardEquation

theorem contextGuardEquation_mem
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    {sort : Sigma.SortId}
    (name : ManySorted.ContextVar Sigma.SortId context sort) :
    contextGuardEquation (⟨sort, name⟩ : ContextEntry context) ∈
      contextGuardEquations context :=
  List.mem_map_of_mem (contextEntry_mem name)

def translateExistenceAtom
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (atom : ExistenceAtom Sigma context) :
    Conditional.Equation (encodedTotalSignature Sigma)
      (LiftDataVar (ManySorted.ContextVar Sigma.SortId context)) :=
  truthEquation
    (encodedExistenceTerm atom.sort
      (encodeDataTerm atom.left) (encodeDataTerm atom.right))
    encodedTrueTerm

abbrev translateQuasiEquation
    {Sigma : ManySorted.Signature.{u}}
    (equation : QuasiEquation Sigma) :
    Conditional.Clause (encodedTotalSignature Sigma) where
  Var := LiftDataVar
    (ManySorted.ContextVar Sigma.SortId equation.context)
  premises := contextGuardEquations equation.context ++
    equation.premises.map translateExistenceAtom
  conclusion := translateExistenceAtom equation.conclusion

def translatedConditionalTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    Conditional.Theory (encodedTotalSignature Sigma) :=
  fun clause => IsGammaClause clause \/
    Exists fun equation =>
      theory equation /\ translateQuasiEquation equation = clause

def liftDataAssignment
    {Sigma : ManySorted.Signature.{u}}
    {Var : Sigma.SortId -> Type u}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (rho : ManySorted.Assignment Sigma Var M.Data) :
    Conditional.Assignment (encodedTotalSignature Sigma)
      (LiftDataVar Var) (EncodedAlg.toConditional M).Carrier
  | .data sort, name => rho sort name
  | .truth, name => nomatch name.down

theorem encodeDataTerm_eval
    {Sigma : ManySorted.Signature.{u}}
    {Var : Sigma.SortId -> Type u}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (rho : ManySorted.Assignment Sigma Var M.Data)
    {sort : Sigma.SortId}
    (term : ManySorted.Term Sigma Var sort) :
    (encodeDataTerm term).eval (EncodedAlg.toConditional M)
        (liftDataAssignment M rho) =
      term.evalEncoded M rho := by
  induction term with
  | var name => rfl
  | total op args ih =>
      change M.evalTotal op
          (fun i => Conditional.Term.eval (EncodedAlg.toConditional M)
            (liftDataAssignment M rho) (encodeDataTerm (args i))) =
        M.evalTotal op (fun i => ManySorted.Term.evalEncoded M rho (args i))
      exact congrArg (M.evalTotal op) (funext ih)
  | partialApp op args ih =>
      change M.evalPartialSymbol op
          (fun i => Conditional.Term.eval (EncodedAlg.toConditional M)
            (liftDataAssignment M rho) (encodeDataTerm (args i))) =
        M.evalPartialSymbol op
          (fun i => ManySorted.Term.evalEncoded M rho (args i))
      exact congrArg (M.evalPartialSymbol op) (funext ih)

theorem translateExistenceAtom_sat_iff_encoded
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (rho : ManySorted.ContextAssignment Sigma M.Data context)
    (atom : ExistenceAtom Sigma context) :
    (translateExistenceAtom atom).Sat (EncodedAlg.toConditional M)
        (liftDataAssignment M rho) <->
      (ManySorted.alpha atom.toFormula).Sat M rho := by
  change M.existenceEq atom.sort
      (Conditional.Term.eval (EncodedAlg.toConditional M)
        (liftDataAssignment M rho) (encodeDataTerm atom.left))
      (Conditional.Term.eval (EncodedAlg.toConditional M)
        (liftDataAssignment M rho) (encodeDataTerm atom.right)) =
      M.trueValue <->
    M.existenceEq atom.sort
      (ManySorted.Term.evalEncoded M rho atom.left)
      (ManySorted.Term.evalEncoded M rho atom.right) = M.trueValue
  rw [encodeDataTerm_eval, encodeDataTerm_eval]

theorem translateExistenceAtom_sat_iff_partial
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (rho : ManySorted.ContextAssignment Sigma
      (ManySorted.beta M hM).Carrier context)
    (atom : ExistenceAtom Sigma context) :
    (translateExistenceAtom atom).Sat (EncodedAlg.toConditional M)
        (liftDataAssignment M (ManySorted.liftBetaAssignment hM rho)) <->
      atom.Sat (ManySorted.beta M hM) rho := by
  exact (translateExistenceAtom_sat_iff_encoded M
    (ManySorted.liftBetaAssignment hM rho) atom).trans
      (ManySorted.alpha_satisfaction_condition M hM rho atom.toFormula).symm

def betaAssignmentOfGuards
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (rho : Conditional.Assignment (encodedTotalSignature Sigma)
      (LiftDataVar (ManySorted.ContextVar Sigma.SortId context))
      (EncodedAlg.toConditional M).Carrier)
    (hGuards : forall guard, guard ∈ contextGuardEquations context ->
      guard.Sat (EncodedAlg.toConditional M) rho) :
    ManySorted.ContextAssignment Sigma (ManySorted.beta M hM).Carrier
      context :=
  fun sort name =>
    ⟨rho (.data sort) name, by
      have hGuard := hGuards
        (contextGuardEquation (⟨sort, name⟩ : ContextEntry context))
        (contextGuardEquation_mem name)
      change M.existenceEq sort
          (rho (.data sort) name) (rho (.data sort) name) = M.trueValue
        at hGuard
      exact hGuard⟩

theorem lift_betaAssignmentOfGuards
    {Sigma : ManySorted.Signature.{u}}
    {context : List Sigma.SortId}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (rho : Conditional.Assignment (encodedTotalSignature Sigma)
      (LiftDataVar (ManySorted.ContextVar Sigma.SortId context))
      (EncodedAlg.toConditional M).Carrier)
    (hGuards : forall guard, guard ∈ contextGuardEquations context ->
      guard.Sat (EncodedAlg.toConditional M) rho) :
    liftDataAssignment M (ManySorted.liftBetaAssignment hM
      (betaAssignmentOfGuards M hM rho hGuards)) = rho := by
  funext sort name
  cases sort with
  | data sort => rfl
  | truth => exact nomatch name.down

theorem translateQuasiEquation_sat_iff_partial
    {Sigma : ManySorted.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (equation : QuasiEquation Sigma) :
    (translateQuasiEquation equation).Sat (EncodedAlg.toConditional M) <->
      equation.Sat (ManySorted.beta M hM) := by
  constructor
  · intro hClause rho hPremises
    apply (translateExistenceAtom_sat_iff_partial M hM rho
      equation.conclusion).1
    apply hClause
      (liftDataAssignment M (ManySorted.liftBetaAssignment hM rho))
    intro premise hPremise
    rw [List.mem_append] at hPremise
    rcases hPremise with hGuard | hTranslated
    · rcases List.mem_map.1 hGuard with ⟨entry, hEntry, rfl⟩
      rcases entry with ⟨sort, name⟩
      change M.existenceEq sort (rho sort name).1 (rho sort name).1 =
        M.trueValue
      exact (rho sort name).property
    · rcases List.mem_map.1 hTranslated with
        ⟨partialPremise, hPartialPremise, rfl⟩
      exact (translateExistenceAtom_sat_iff_partial M hM rho
        partialPremise).2
          (hPremises partialPremise hPartialPremise)
  · intro hEquation rho hPremises
    have hGuards : forall guard,
        guard ∈ contextGuardEquations equation.context ->
          guard.Sat (EncodedAlg.toConditional M) rho := by
      intro guard hGuard
      exact hPremises guard (List.mem_append_left _ hGuard)
    let betaRho := betaAssignmentOfGuards M hM rho hGuards
    have hAssignments := lift_betaAssignmentOfGuards M hM rho hGuards
    have hPartialConclusion :
        equation.conclusion.Sat (ManySorted.beta M hM) betaRho := by
      apply hEquation betaRho
      intro premise hPremise
      apply (translateExistenceAtom_sat_iff_partial M hM betaRho
        premise).1
      rw [hAssignments]
      exact hPremises (translateExistenceAtom premise)
        (List.mem_append_right _ (List.mem_map_of_mem hPremise))
    have hEncodedConclusion :=
      (translateExistenceAtom_sat_iff_partial M hM betaRho
        equation.conclusion).2 hPartialConclusion
    rw [hAssignments] at hEncodedConclusion
    exact hEncodedConclusion

theorem models_translatedConditionalTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma)
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (hTheory : forall equation, theory equation ->
      equation.Sat (ManySorted.beta M hM)) :
    Conditional.Models (EncodedAlg.toConditional M)
      (translatedConditionalTheory theory) := by
  intro clause hClause
  rcases hClause with hGamma | ⟨equation, hEquation, rfl⟩
  · exact modelsGamma_of_satisfiesGamma M hM clause hGamma
  · exact (translateQuasiEquation_sat_iff_partial M hM equation).2
      (hTheory equation hEquation)

theorem quasi_models_of_models_translatedConditionalTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma)
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hM : ManySorted.SatisfiesGamma M)
    (hModels : Conditional.Models (EncodedAlg.toConditional M)
      (translatedConditionalTheory theory)) :
    forall equation, theory equation ->
      equation.Sat (ManySorted.beta M hM) := by
  intro equation hEquation
  apply (translateQuasiEquation_sat_iff_partial M hM equation).1
  exact hModels (translateQuasiEquation equation)
    (Or.inr ⟨equation, hEquation, rfl⟩)

theorem satisfiesGamma_of_models_translatedConditionalTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma)
    (M : ManySorted.EncodedAlg.{u,v,v} Sigma)
    (hModels : Conditional.Models (EncodedAlg.toConditional M)
      (translatedConditionalTheory theory)) :
    ManySorted.SatisfiesGamma M :=
  satisfiesGamma_of_modelsGamma M (by
    intro clause hClause
    exact hModels clause (Or.inl hClause))

theorem finTwo_eta
    {alpha : Type v}
    (values : Fin 2 -> alpha) :
    values = Fin.cases (values 0) (fun _ => values 1) := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro impossible
  exact Fin.elim0 impossible

def conditionalHomToEncodedTarget
    {Sigma : ManySorted.Signature.{u}}
    {A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)}
    {M : ManySorted.EncodedAlg.{u,w,w} Sigma}
    (hom : Conditional.Hom A (EncodedAlg.toConditional M)) :
    ManySorted.EncodedHom (conditionalToEncodedAlg A) M where
  dataMap sort := hom.toFun (.data sort)
  truthMap := hom.toFun .truth
  map_total op args := hom.map_op (.total op) args
  map_partial_symbol op args := hom.map_op (.partialSymbol op) args
  map_existenceEq sort left right := by
    have h := hom.map_op (.existenceEq sort)
      (Fin.cases left (fun _ => right))
    have hOne :
        Fin.cases left (fun _ => right) (1 : Fin 2) = right := rfl
    simpa only [Fin.cases_zero, hOne] using h
  map_true := by
    have h := hom.map_op .trueValue (fun i => nomatch i)
    simpa [conditionalToEncodedAlg, EncodedAlg.toConditional] using h

def encodedHomFromConditionalSource
    {Sigma : ManySorted.Signature.{u}}
    {A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)}
    {M : ManySorted.EncodedAlg.{u,w,w} Sigma}
    (hom : ManySorted.EncodedHom (conditionalToEncodedAlg A) M) :
    Conditional.Hom A (EncodedAlg.toConditional M) where
  toFun
    | .data sort => hom.dataMap sort
    | .truth => hom.truthMap
  map_op := by
    intro op args
    cases op with
    | total op => exact hom.map_total op args
    | partialSymbol op => exact hom.map_partial_symbol op args
    | existenceEq sort =>
        change (Fin 2 -> A.Carrier (.data sort)) at args
        change hom.truthMap (A.eval (.existenceEq sort) args) =
          M.existenceEq sort (hom.dataMap sort (args 0))
            (hom.dataMap sort (args 1))
        rw [finTwo_eta args]
        exact hom.map_existenceEq sort (args 0) (args 1)
    | trueValue =>
        change hom.truthMap (A.eval .trueValue args) = M.trueValue
        have hArgs : args = (fun i => nomatch i) := by
          funext i
          exact Fin.elim0 i
        rw [hArgs]
        exact hom.map_true

theorem encodedHomFromConditionalSource_toEncodedTarget
    {Sigma : ManySorted.Signature.{u}}
    {A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)}
    {M : ManySorted.EncodedAlg.{u,w,w} Sigma}
    (hom : Conditional.Hom A (EncodedAlg.toConditional M)) :
    encodedHomFromConditionalSource (conditionalHomToEncodedTarget hom) = hom := by
  apply Conditional.Hom.ext
  funext sort value
  cases sort <;> rfl

theorem conditionalHomToEncodedTarget_fromConditionalSource
    {Sigma : ManySorted.Signature.{u}}
    {A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)}
    {M : ManySorted.EncodedAlg.{u,w,w} Sigma}
    (hom : ManySorted.EncodedHom (conditionalToEncodedAlg A) M) :
    conditionalHomToEncodedTarget (encodedHomFromConditionalSource hom) = hom := by
  apply ManySorted.EncodedHom.ext
  · rfl
  · rfl

def roundtripCarrierTo
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)) :
    forall sort : EncodedSort Sigma,
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier sort ->
        A.Carrier sort
  | .data _, value => value
  | .truth, value => value

def roundtripCarrierFrom
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)) :
    forall sort : EncodedSort Sigma,
      A.Carrier sort ->
        (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier sort
  | .data _, value => value
  | .truth, value => value

@[simp] theorem roundtripCarrierTo_from
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (sort : EncodedSort Sigma)
    (value : A.Carrier sort) :
    roundtripCarrierTo A sort (roundtripCarrierFrom A sort value) = value := by
  cases sort <;> rfl

@[simp] theorem roundtripCarrierFrom_to
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (sort : EncodedSort Sigma)
    (value :
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier sort) :
    roundtripCarrierFrom A sort (roundtripCarrierTo A sort value) = value := by
  cases sort <;> rfl

theorem roundtripCarrierTo_injective
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (sort : EncodedSort Sigma) :
    Function.Injective (roundtripCarrierTo A sort) := by
  intro left right h
  have := congrArg (roundtripCarrierFrom A sort) h
  simpa using this

def roundtripAssignmentTo
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (rho : Conditional.Assignment (encodedTotalSignature Sigma) Var
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier) :
    Conditional.Assignment (encodedTotalSignature Sigma) Var A.Carrier :=
  fun sort name => roundtripCarrierTo A sort (rho sort name)

def roundtripAssignmentFrom
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (rho : Conditional.Assignment (encodedTotalSignature Sigma) Var A.Carrier) :
    Conditional.Assignment (encodedTotalSignature Sigma) Var
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier :=
  fun sort name => roundtripCarrierFrom A sort (rho sort name)

theorem roundtripAssignmentTo_from
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (rho : Conditional.Assignment (encodedTotalSignature Sigma) Var A.Carrier) :
    roundtripAssignmentTo A (roundtripAssignmentFrom A rho) = rho := by
  funext sort name
  exact roundtripCarrierTo_from A sort (rho sort name)

def roundtripHom
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma)) :
    Conditional.Hom
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)) A where
  toFun := roundtripCarrierTo A
  map_op := by
    intro op args
    cases op with
    | total op => rfl
    | partialSymbol op => rfl
    | existenceEq sort =>
        change A.eval (.existenceEq sort)
            (Fin.cases (args 0) (fun _ => args 1)) =
          A.eval (.existenceEq sort) args
        apply congrArg (A.eval (.existenceEq sort))
        funext i
        refine Fin.cases rfl ?_ i
        intro j
        refine Fin.cases rfl ?_ j
        intro impossible
        exact Fin.elim0 impossible
    | trueValue =>
        have hArgs : args = (fun i => nomatch i) := by
          funext i
          exact Fin.elim0 i
        subst args
        change A.eval .trueValue (fun i => nomatch i) = A.eval .trueValue _
        apply congrArg (A.eval .trueValue)
        funext i
        exact Fin.elim0 i

theorem term_eval_roundtrip
    {Sigma : ManySorted.Signature.{u}}
    {Var : EncodedSort Sigma -> Type u}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (rho : Conditional.Assignment (encodedTotalSignature Sigma) Var
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier)
    {sort : EncodedSort Sigma}
    (term : Conditional.Term (encodedTotalSignature Sigma) Var sort) :
    roundtripCarrierTo A sort
        (term.eval (EncodedAlg.toConditional (conditionalToEncodedAlg A)) rho) =
      term.eval A (roundtripAssignmentTo A rho) := by
  exact (roundtripHom A).map_term rho term

theorem equation_sat_roundtrip
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    {Var : EncodedSort Sigma -> Type u}
    (equation : Conditional.Equation (encodedTotalSignature Sigma) Var)
    (rho : Conditional.Assignment (encodedTotalSignature Sigma) Var
      (EncodedAlg.toConditional (conditionalToEncodedAlg A)).Carrier) :
    equation.Sat (EncodedAlg.toConditional (conditionalToEncodedAlg A)) rho <->
      equation.Sat A (roundtripAssignmentTo A rho) := by
  unfold Conditional.Equation.Sat
  constructor
  · intro h
    calc
      _ = roundtripCarrierTo A equation.sort
          (equation.left.eval
            (EncodedAlg.toConditional (conditionalToEncodedAlg A)) rho) :=
        (term_eval_roundtrip A rho equation.left).symm
      _ = roundtripCarrierTo A equation.sort
          (equation.right.eval
            (EncodedAlg.toConditional (conditionalToEncodedAlg A)) rho) :=
        congrArg (roundtripCarrierTo A equation.sort) h
      _ = _ := term_eval_roundtrip A rho equation.right
  · intro h
    apply roundtripCarrierTo_injective A equation.sort
    rw [term_eval_roundtrip, term_eval_roundtrip]
    exact h

theorem clause_sat_roundtrip
    {Sigma : ManySorted.Signature.{u}}
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (clause : Conditional.Clause (encodedTotalSignature Sigma)) :
    clause.Sat (EncodedAlg.toConditional (conditionalToEncodedAlg A)) <->
      clause.Sat A := by
  constructor
  · intro hSat rho hPremises
    let lifted := roundtripAssignmentFrom A rho
    have hAssignment : roundtripAssignmentTo A lifted = rho :=
      roundtripAssignmentTo_from A rho
    have hConclusion := (equation_sat_roundtrip A clause.conclusion lifted).1
      (hSat lifted (fun premise hPremise =>
        (equation_sat_roundtrip A premise lifted).2 (by
          rw [hAssignment]
          exact hPremises premise hPremise)))
    rw [hAssignment] at hConclusion
    exact hConclusion
  · intro hSat rho hPremises
    exact (equation_sat_roundtrip A clause.conclusion rho).2
      (hSat (roundtripAssignmentTo A rho) (fun premise hPremise =>
        (equation_sat_roundtrip A premise rho).1
          (hPremises premise hPremise)))

theorem models_roundtrip_translatedConditionalTheory
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma)
    (A : Conditional.Alg.{u,v} (encodedTotalSignature Sigma))
    (hModels : Conditional.Models A
      (translatedConditionalTheory theory)) :
    Conditional.Models
      (EncodedAlg.toConditional (conditionalToEncodedAlg A))
      (translatedConditionalTheory theory) := by
  intro clause hClause
  exact (clause_sat_roundtrip A clause).2 (hModels clause hClause)

/-! ## Initial encoded and partial models -/

noncomputable abbrev initialConditionalModel
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    Conditional.Alg.{u,u} (encodedTotalSignature Sigma) :=
  Conditional.termModel.{u,u} (translatedConditionalTheory theory)

noncomputable abbrev initialEncodedModel
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) : ManySorted.EncodedAlg.{u,u,u} Sigma :=
  conditionalToEncodedAlg (initialConditionalModel theory)

theorem initialEncodedModel_models_conditional
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    Conditional.Models
      (EncodedAlg.toConditional (initialEncodedModel theory))
      (translatedConditionalTheory theory) := by
  apply models_roundtrip_translatedConditionalTheory theory
  exact Conditional.termModel_models (translatedConditionalTheory theory)

theorem initialEncodedModel_satisfiesGamma
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    ManySorted.SatisfiesGamma (initialEncodedModel theory) :=
  satisfiesGamma_of_models_translatedConditionalTheory theory
    (initialEncodedModel theory)
    (initialEncodedModel_models_conditional theory)

theorem initialEncodedModel_models_translation
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    ManySorted.ModelsEncodedTranslation (initialEncodedModel theory)
      theory.toPartialTheory := by
  let hGamma := initialEncodedModel_satisfiesGamma theory
  apply (ManySorted.beta_models_partial_iff_encoded_translation
    (initialEncodedModel theory) hGamma theory.toPartialTheory).1
  apply (models_quasiTheory_iff theory
    (ManySorted.beta (initialEncodedModel theory) hGamma)).2
  exact quasi_models_of_models_translatedConditionalTheory theory
    (initialEncodedModel theory) hGamma
    (initialEncodedModel_models_conditional theory)

theorem initialEncodedModel_is_initial
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    ManySorted.IsInitialEncodedModel.{u,u} theory.toPartialTheory
      (initialEncodedModel theory) := by
  let hGamma := initialEncodedModel_satisfiesGamma theory
  refine
    { satisfiesGamma := hGamma
      models := initialEncodedModel_models_translation theory
      hom_unique := ?_ }
  intro N hNGamma hNModels
  have hNPartial :
      ManySorted.ModelsPartialTheory (ManySorted.beta N hNGamma)
        theory.toPartialTheory :=
    (ManySorted.beta_models_partial_iff_encoded_translation N hNGamma
      theory.toPartialTheory).2 hNModels
  have hNQuasi : forall equation, theory equation ->
      equation.Sat (ManySorted.beta N hNGamma) :=
    (models_quasiTheory_iff theory (ManySorted.beta N hNGamma)).1 hNPartial
  have hNConditional :
      Conditional.Models (EncodedAlg.toConditional N)
        (translatedConditionalTheory theory) :=
    models_translatedConditionalTheory theory N hNGamma hNQuasi
  let initialMapConditional := Conditional.termModelHom
    (translatedConditionalTheory theory) (EncodedAlg.toConditional N)
    hNConditional
  let initialMap := conditionalHomToEncodedTarget initialMapConditional
  refine ⟨initialMap, ?_⟩
  intro candidate
  have hUniqueConditional :
      encodedHomFromConditionalSource candidate = initialMapConditional :=
    Conditional.termModelHom_unique
      (translatedConditionalTheory theory) (EncodedAlg.toConditional N)
      hNConditional (encodedHomFromConditionalSource candidate)
  calc
    candidate = conditionalHomToEncodedTarget
        (encodedHomFromConditionalSource candidate) :=
      (conditionalHomToEncodedTarget_fromConditionalSource candidate).symm
    _ = conditionalHomToEncodedTarget initialMapConditional :=
      congrArg conditionalHomToEncodedTarget hUniqueConditional
    _ = initialMap := rfl

/-- Fixed-signature, operations-only formalization of the initial-model
conclusion used in Diaconescu's Corollary 4.2 for quasi-existence equations.
The result is universe-bounded and makes no claim about institution-level
signature morphisms or proof-theoretic completeness. -/
theorem quasiTheory_has_initial_partial_model
    {Sigma : ManySorted.Signature.{u}}
    (theory : QuasiTheory Sigma) :
    Exists fun D : ManySorted.PartialAlg.{u,u} Sigma =>
      ManySorted.IsInitialPartialModel.{u,u} theory.toPartialTheory D := by
  let hInitial := initialEncodedModel_is_initial theory
  exact ⟨ManySorted.beta (initialEncodedModel theory)
      hInitial.satisfiesGamma,
    ManySorted.beta_of_initial_encoded_is_initial theory.toPartialTheory
      (initialEncodedModel theory) hInitial⟩

end InitialExistence
end Diaconescu
end Resolution
