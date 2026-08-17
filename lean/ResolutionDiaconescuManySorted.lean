import Std

universe u v w x y

namespace Resolution
namespace Diaconescu
namespace ManySorted

noncomputable local instance classicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Many-sorted partial algebra signatures

Operations carry a finite arity, a sort for every argument position, and a
result sort.  Total and partial operation symbols are kept separate, matching
the `TF/PF` distinction in Diaconescu's encoding.
-/

set_option linter.checkUnivs false in
structure Signature where
  SortId : Type u
  TotalOp : Type u
  PartialOp : Type u
  totalArity : TotalOp -> Nat
  totalArgSort : forall f : TotalOp, Fin (totalArity f) -> SortId
  totalResultSort : TotalOp -> SortId
  partialArity : PartialOp -> Nat
  partialArgSort : forall f : PartialOp, Fin (partialArity f) -> SortId
  partialResultSort : PartialOp -> SortId

abbrev TotalArgs
    (Sigma : Signature.{u})
    (A : Sigma.SortId -> Type v)
    (f : Sigma.TotalOp) : Type v :=
  forall i : Fin (Sigma.totalArity f), A (Sigma.totalArgSort f i)

abbrev PartialArgs
    (Sigma : Signature.{u})
    (A : Sigma.SortId -> Type v)
    (f : Sigma.PartialOp) : Type v :=
  forall i : Fin (Sigma.partialArity f), A (Sigma.partialArgSort f i)

/-- Terms over a sort-indexed family of variables.  Both total and partial
symbols are syntactically ordinary operations; partiality enters only during
evaluation in a partial algebra. -/
inductive Term
    (Sigma : Signature.{u})
    (Var : Sigma.SortId -> Type x) : Sigma.SortId -> Type (max u x) where
  | var {s : Sigma.SortId} (name : Var s) : Term Sigma Var s
  | total (f : Sigma.TotalOp)
      (args : forall i : Fin (Sigma.totalArity f),
        Term Sigma Var (Sigma.totalArgSort f i)) :
      Term Sigma Var (Sigma.totalResultSort f)
  | partialApp (f : Sigma.PartialOp)
      (args : forall i : Fin (Sigma.partialArity f),
        Term Sigma Var (Sigma.partialArgSort f i)) :
      Term Sigma Var (Sigma.partialResultSort f)

/-- A many-sorted partial algebra. -/
structure PartialAlg (Sigma : Signature.{u}) where
  Carrier : Sigma.SortId -> Type v
  evalTotal : forall f : Sigma.TotalOp,
    TotalArgs Sigma Carrier f -> Carrier (Sigma.totalResultSort f)
  evalPartial : forall f : Sigma.PartialOp,
    PartialArgs Sigma Carrier f -> Option (Carrier (Sigma.partialResultSort f))

abbrev Assignment
    (Sigma : Signature.{u})
    (Var : Sigma.SortId -> Type x)
    (A : Sigma.SortId -> Type v) : Type (max u x v) :=
  forall s : Sigma.SortId, Var s -> A s

/-- Evaluate every argument of an operation, recording the existence of a
value at each finite argument position. -/
def AllSome
    {n : Nat}
    {S : Fin n -> Type v}
    (values : forall i : Fin n, Option (S i)) : Prop :=
  forall i : Fin n, Exists fun value : S i => values i = some value

noncomputable def someValue
    {n : Nat}
    {S : Fin n -> Type v}
    {values : forall i : Fin n, Option (S i)}
    (h : AllSome values)
    (i : Fin n) : S i :=
  Classical.choose (h i)

theorem someValue_spec
    {n : Nat}
    {S : Fin n -> Type v}
    {values : forall i : Fin n, Option (S i)}
    (h : AllSome values)
    (i : Fin n) :
    values i = some (someValue h i) :=
  Classical.choose_spec (h i)

/-- Partial evaluation of many-sorted terms. -/
noncomputable def Term.evalPartial
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (A : PartialAlg.{u,v} Sigma)
    (rho : Assignment Sigma Var A.Carrier) :
    {s : Sigma.SortId} -> Term Sigma Var s -> Option (A.Carrier s)
  | _, .var name => some (rho _ name)
  | _, .total f args =>
      let evaluated := fun i => evalPartial A rho (args i)
      if h : AllSome evaluated then
        some (A.evalTotal f (fun i => someValue h i))
      else
        none
  | _, .partialApp f args =>
      let evaluated := fun i => evalPartial A rho (args i)
      if h : AllSome evaluated then
        A.evalPartial f (fun i => someValue h i)
      else
        none

/-- Homomorphisms preserve total operations and every defined partial
application. -/
structure PartialHom
    {Sigma : Signature.{u}}
    (A : PartialAlg.{u,v} Sigma)
    (B : PartialAlg.{u,w} Sigma) where
  toFun : forall s : Sigma.SortId, A.Carrier s -> B.Carrier s
  map_total : forall (f : Sigma.TotalOp) (args : TotalArgs Sigma A.Carrier f),
    toFun _ (A.evalTotal f args) =
      B.evalTotal f (fun i => toFun _ (args i))
  map_partial : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma A.Carrier f)
      (result : A.Carrier (Sigma.partialResultSort f)),
    A.evalPartial f args = some result ->
      B.evalPartial f (fun i => toFun _ (args i)) = some (toFun _ result)

/-!
## The encoded total models and the beta reduct
-/

set_option linter.checkUnivs false in
/-- A total algebra for Diaconescu's encoded signature.  Symbols originating
from `PF` are total on `Data`; their partial behavior is recovered by `beta`.
The extra `Truth` sort carries existence equality and its distinguished true
value. -/
structure EncodedAlg (Sigma : Signature.{u}) where
  Data : Sigma.SortId -> Type v
  Truth : Type w
  evalTotal : forall f : Sigma.TotalOp,
    TotalArgs Sigma Data f -> Data (Sigma.totalResultSort f)
  evalPartialSymbol : forall f : Sigma.PartialOp,
    PartialArgs Sigma Data f -> Data (Sigma.partialResultSort f)
  existenceEq : forall s : Sigma.SortId, Data s -> Data s -> Truth
  trueValue : Truth

def AllDefinedTotal
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma M.Data f) : Prop :=
  forall i : Fin (Sigma.totalArity f),
    M.existenceEq _ (args i) (args i) = M.trueValue

def AllDefinedPartial
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma M.Data f) : Prop :=
  forall i : Fin (Sigma.partialArity f),
    M.existenceEq _ (args i) (args i) = M.trueValue

/-- The Horn axioms `Gamma`.  The first and fourth fields together say that
total symbols preserve and reflect definedness; partial symbols only reflect
definedness. -/
structure SatisfiesGamma
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma) : Prop where
  total_preserves_defined : forall (f : Sigma.TotalOp)
      (args : TotalArgs Sigma M.Data f),
    AllDefinedTotal M f args ->
      M.existenceEq _ (M.evalTotal f args) (M.evalTotal f args) = M.trueValue
  equality_defined_left : forall (s : Sigma.SortId) (x y : M.Data s),
    M.existenceEq s x y = M.trueValue ->
      M.existenceEq s x x = M.trueValue
  equality_sound : forall (s : Sigma.SortId) (x y : M.Data s),
    M.existenceEq s x y = M.trueValue -> x = y
  total_reflects_defined : forall (f : Sigma.TotalOp)
      (args : TotalArgs Sigma M.Data f),
    M.existenceEq _ (M.evalTotal f args) (M.evalTotal f args) = M.trueValue ->
      AllDefinedTotal M f args
  partial_reflects_defined : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma M.Data f),
    M.existenceEq _ (M.evalPartialSymbol f args)
        (M.evalPartialSymbol f args) = M.trueValue ->
      AllDefinedPartial M f args

/-- The elements marked as defined at a data sort. -/
abbrev DefinedData
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (s : Sigma.SortId) :=
  {x : M.Data s // M.existenceEq s x x = M.trueValue}

/-- Recover a many-sorted partial algebra from a model of `Gamma`. -/
noncomputable def beta
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) : PartialAlg.{u,v} Sigma where
  Carrier := DefinedData M
  evalTotal := fun f args =>
    ⟨M.evalTotal f (fun i => (args i).1),
      hM.total_preserves_defined f (fun i => (args i).1)
        (fun i => (args i).property)⟩
  evalPartial := fun f args =>
    let result := M.evalPartialSymbol f (fun i => (args i).1)
    if hresult : M.existenceEq _ result result = M.trueValue then
      some ⟨result, hresult⟩
    else
      none

attribute [reducible] beta

theorem beta_partial_eq_some_iff
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (DefinedData M) f)
    (result : DefinedData M (Sigma.partialResultSort f)) :
    (beta M hM).evalPartial f args = some result <->
      M.evalPartialSymbol f (fun i => (args i).1) = result.1 := by
  change
    (if hresult : M.existenceEq _
        (M.evalPartialSymbol f (fun i => (args i).1))
        (M.evalPartialSymbol f (fun i => (args i).1)) = M.trueValue then
      some ⟨M.evalPartialSymbol f (fun i => (args i).1), hresult⟩
    else none) = some result <->
      M.evalPartialSymbol f (fun i => (args i).1) = result.1
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  · rename_i hNot
    constructor
    · simp
    · intro hValue
      apply False.elim
      apply hNot
      simpa [hValue] using result.property

theorem beta_partial_eq_none_iff
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (DefinedData M) f) :
    (beta M hM).evalPartial f args = none <->
      Not (M.existenceEq _
        (M.evalPartialSymbol f (fun i => (args i).1))
        (M.evalPartialSymbol f (fun i => (args i).1)) = M.trueValue) := by
  unfold beta
  dsimp
  by_cases hresult : M.existenceEq _
      (M.evalPartialSymbol f (fun i => (args i).1))
      (M.evalPartialSymbol f (fun i => (args i).1)) = M.trueValue
  · simp [hresult]
  · simp [hresult]

/-- Homomorphisms of encoded total algebras. -/
structure EncodedHom
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (N : EncodedAlg.{u,x,y} Sigma) where
  dataMap : forall s : Sigma.SortId, M.Data s -> N.Data s
  truthMap : M.Truth -> N.Truth
  map_total : forall (f : Sigma.TotalOp) (args : TotalArgs Sigma M.Data f),
    dataMap _ (M.evalTotal f args) =
      N.evalTotal f (fun i => dataMap _ (args i))
  map_partial_symbol : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma M.Data f),
    dataMap _ (M.evalPartialSymbol f args) =
      N.evalPartialSymbol f (fun i => dataMap _ (args i))
  map_existenceEq : forall (s : Sigma.SortId) (a b : M.Data s),
    truthMap (M.existenceEq s a b) =
      N.existenceEq s (dataMap s a) (dataMap s b)
  map_true : truthMap M.trueValue = N.trueValue

@[ext] theorem EncodedHom.ext
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    {F G : EncodedHom M N}
    (hData : F.dataMap = G.dataMap)
    (hTruth : F.truthMap = G.truthMap) : F = G := by
  cases F
  cases G
  cases hData
  cases hTruth
  rfl

def betaMap
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (F : EncodedHom M N) :
    forall s : Sigma.SortId, DefinedData M s -> DefinedData N s :=
  fun s a =>
    ⟨F.dataMap s a.1, by
      calc
        N.existenceEq s (F.dataMap s a.1) (F.dataMap s a.1) =
            F.truthMap (M.existenceEq s a.1 a.1) :=
          (F.map_existenceEq s a.1 a.1).symm
        _ = F.truthMap M.trueValue := congrArg F.truthMap a.property
        _ = N.trueValue := F.map_true⟩

/-- `beta` is functorial on encoded homomorphisms. -/
noncomputable def betaHom
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (hM : SatisfiesGamma M)
    (hN : SatisfiesGamma N)
    (F : EncodedHom M N) : PartialHom (beta M hM) (beta N hN) where
  toFun := betaMap F
  map_total := by
    intro f args
    apply Subtype.ext
    exact F.map_total f (fun i => (args i).1)
  map_partial := by
    intro f args result hEval
    apply (beta_partial_eq_some_iff N hN f
      (fun i => betaMap F _ (args i)) (betaMap F _ result)).2
    change N.evalPartialSymbol f (fun i => F.dataMap _ (args i).1) =
      F.dataMap _ result.1
    rw [<- F.map_partial_symbol]
    exact congrArg (F.dataMap _)
      ((beta_partial_eq_some_iff M hM f args result).1 hEval)

/-!
## Syntax, the alpha translation, and satisfaction
-/

/-- Total evaluation of a partial-algebra term in an encoded model: symbols
from `PF` use their totalized interpretation. -/
def Term.evalEncoded
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (M : EncodedAlg.{u,v,w} Sigma)
    (rho : Assignment Sigma Var M.Data) :
    {s : Sigma.SortId} -> Term Sigma Var s -> M.Data s
  | _, .var name => rho _ name
  | _, .total f args =>
      M.evalTotal f (fun i => evalEncoded M rho (args i))
  | _, .partialApp f args =>
      M.evalPartialSymbol f (fun i => evalEncoded M rho (args i))

/-- Lift an assignment into a `beta` reduct to the underlying total data
carrier. -/
def liftBetaAssignment
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    {M : EncodedAlg.{u,v,w} Sigma}
    (hM : SatisfiesGamma M)
    (rho : Assignment Sigma Var (beta M hM).Carrier) :
    Assignment Sigma Var M.Data :=
  fun _ name => (rho _ name).1

/-- Typed de Bruijn variables for a many-sorted context. -/
inductive ContextVar
    (SortId : Type u) : List SortId -> SortId -> Type u where
  | here {context : List SortId} {s : SortId} :
      ContextVar SortId (s :: context) s
  | there {context : List SortId} {s t : SortId}
      (name : ContextVar SortId context s) :
      ContextVar SortId (t :: context) s

abbrev ContextAssignment
    (Sigma : Signature.{u})
    (A : Sigma.SortId -> Type v)
    (context : List Sigma.SortId) :=
  Assignment Sigma (ContextVar Sigma.SortId context) A

def ContextAssignment.extend
    {Sigma : Signature.{u}}
    {A : Sigma.SortId -> Type v}
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma A context)
    {bound : Sigma.SortId}
    (value : A bound) : ContextAssignment Sigma A (bound :: context)
  | _, .here => value
  | _, .there name => rho _ name

/-- Formulas of partial algebra with existence equality and total
quantification.  Conjunction and negation generate the usual Boolean
connectives. -/
inductive Formula
    (Sigma : Signature.{u}) : List Sigma.SortId -> Type u where
  | existenceEquality {context : List Sigma.SortId} {s : Sigma.SortId}
      (left right : Term Sigma (ContextVar Sigma.SortId context) s) :
      Formula Sigma context
  | conjunction {context : List Sigma.SortId}
      (left right : Formula Sigma context) : Formula Sigma context
  | negation {context : List Sigma.SortId}
      (body : Formula Sigma context) : Formula Sigma context
  | universal {context : List Sigma.SortId} (s : Sigma.SortId)
      (body : Formula Sigma (s :: context)) : Formula Sigma context

/-- Truth-sort terms needed by the image of `alpha`. -/
inductive TruthTerm
    (Sigma : Signature.{u})
    (context : List Sigma.SortId) : Type u where
  | trueValue : TruthTerm Sigma context
  | existenceEquality {s : Sigma.SortId}
      (left right : Term Sigma (ContextVar Sigma.SortId context) s) :
      TruthTerm Sigma context

/-- The total-algebra formulas produced by `alpha`. -/
inductive EncodedFormula
    (Sigma : Signature.{u}) : List Sigma.SortId -> Type u where
  | truthEquality {context : List Sigma.SortId}
      (left right : TruthTerm Sigma context) : EncodedFormula Sigma context
  | conjunction {context : List Sigma.SortId}
      (left right : EncodedFormula Sigma context) : EncodedFormula Sigma context
  | negation {context : List Sigma.SortId}
      (body : EncodedFormula Sigma context) : EncodedFormula Sigma context
  | implication {context : List Sigma.SortId}
      (antecedent consequent : EncodedFormula Sigma context) :
      EncodedFormula Sigma context
  | universalData {context : List Sigma.SortId} (s : Sigma.SortId)
      (body : EncodedFormula Sigma (s :: context)) : EncodedFormula Sigma context

def TruthTerm.eval
    {Sigma : Signature.{u}}
    {context : List Sigma.SortId}
    (M : EncodedAlg.{u,v,w} Sigma)
    (rho : ContextAssignment Sigma M.Data context) :
    TruthTerm Sigma context -> M.Truth
  | .trueValue => M.trueValue
  | .existenceEquality left right =>
      M.existenceEq _ (left.evalEncoded M rho) (right.evalEncoded M rho)

/-- Tarskian satisfaction for partial formulas. -/
def Formula.Sat
    {Sigma : Signature.{u}}
    {context : List Sigma.SortId}
    (A : PartialAlg.{u,v} Sigma)
    (rho : ContextAssignment Sigma A.Carrier context) :
    Formula Sigma context -> Prop
  | .existenceEquality left right =>
      Exists fun value : A.Carrier _ =>
        left.evalPartial A rho = some value /\
          right.evalPartial A rho = some value
  | .conjunction left right => left.Sat A rho /\ right.Sat A rho
  | .negation body => Not (body.Sat A rho)
  | .universal _ body =>
      forall value, body.Sat A (ContextAssignment.extend rho value)

/-- Tarskian satisfaction for formulas in the encoded total signature. -/
def EncodedFormula.Sat
    {Sigma : Signature.{u}}
    {context : List Sigma.SortId}
    (M : EncodedAlg.{u,v,w} Sigma)
    (rho : ContextAssignment Sigma M.Data context) :
    EncodedFormula Sigma context -> Prop
  | .truthEquality left right => left.eval M rho = right.eval M rho
  | .conjunction left right => left.Sat M rho /\ right.Sat M rho
  | .negation body => Not (body.Sat M rho)
  | .implication antecedent consequent =>
      antecedent.Sat M rho -> consequent.Sat M rho
  | .universalData _ body =>
      forall value, body.Sat M (ContextAssignment.extend rho value)

/-- The guard asserting that the newest bound variable is defined. -/
def newestDefinedGuard
    {Sigma : Signature.{u}}
    {context : List Sigma.SortId}
    (s : Sigma.SortId) : EncodedFormula Sigma (s :: context) :=
  .truthEquality
    (.existenceEquality (.var ContextVar.here) (.var ContextVar.here))
    .trueValue

/-- Diaconescu's sentence translation `alpha`. -/
def alpha
    {Sigma : Signature.{u}}
    {context : List Sigma.SortId} :
    Formula Sigma context -> EncodedFormula Sigma context
  | .existenceEquality left right =>
      .truthEquality (.existenceEquality left right) .trueValue
  | .conjunction left right => .conjunction (alpha left) (alpha right)
  | .negation body => .negation (alpha body)
  | .universal s body =>
      .universalData s (.implication (newestDefinedGuard s) (alpha body))

/-- Lemma 3.3 in the many-sorted setting: whenever a term is defined in the
`beta` reduct, total encoded evaluation has the same underlying value. -/
theorem term_evalPartial_sound
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (rho : Assignment Sigma Var (beta M hM).Carrier)
    {s : Sigma.SortId}
    (term : Term Sigma Var s)
    (result : (beta M hM).Carrier s) :
    term.evalPartial (beta M hM) rho = some result ->
      term.evalEncoded M (liftBetaAssignment hM rho) = result.1 := by
  induction term with
  | var name =>
      intro hEval
      change some (rho _ name) = some result at hEval
      exact congrArg Subtype.val (Option.some.inj hEval)
  | total f args ih =>
      intro hEval
      let evaluated := fun i =>
        Term.evalPartial (beta M hM) rho (args i)
      change (if h : AllSome evaluated then
          some ((beta M hM).evalTotal f (fun i => someValue h i))
        else none) = some result at hEval
      by_cases hArgs : AllSome evaluated
      · rw [dif_pos hArgs] at hEval
        have hResult :
            (beta M hM).evalTotal f (fun i => someValue hArgs i) = result :=
          Option.some.inj hEval
        have hPoint : forall i,
            Term.evalEncoded M (liftBetaAssignment hM rho) (args i) =
              (someValue hArgs i).1 := by
          intro i
          exact ih i (someValue hArgs i) (someValue_spec hArgs i)
        calc
          Term.evalEncoded M (liftBetaAssignment hM rho) (.total f args) =
              M.evalTotal f
                (fun i => Term.evalEncoded M (liftBetaAssignment hM rho) (args i)) :=
            rfl
          _ = M.evalTotal f (fun i => (someValue hArgs i).1) := by
            exact congrArg (M.evalTotal f) (funext hPoint)
          _ = ((beta M hM).evalTotal f
              (fun i => someValue hArgs i)).1 := rfl
          _ = result.1 := congrArg Subtype.val hResult
      · rw [dif_neg hArgs] at hEval
        cases hEval
  | partialApp f args ih =>
      intro hEval
      let evaluated := fun i =>
        Term.evalPartial (beta M hM) rho (args i)
      change (if h : AllSome evaluated then
          (beta M hM).evalPartial f (fun i => someValue h i)
        else none) = some result at hEval
      by_cases hArgs : AllSome evaluated
      · rw [dif_pos hArgs] at hEval
        have hOperation := (beta_partial_eq_some_iff M hM f
          (fun i => someValue hArgs i) result).1 hEval
        have hPoint : forall i,
            Term.evalEncoded M (liftBetaAssignment hM rho) (args i) =
              (someValue hArgs i).1 := by
          intro i
          exact ih i (someValue hArgs i) (someValue_spec hArgs i)
        calc
          Term.evalEncoded M (liftBetaAssignment hM rho) (.partialApp f args) =
              M.evalPartialSymbol f
                (fun i => Term.evalEncoded M (liftBetaAssignment hM rho) (args i)) :=
            rfl
          _ = M.evalPartialSymbol f (fun i => (someValue hArgs i).1) := by
            exact congrArg (M.evalPartialSymbol f) (funext hPoint)
          _ = result.1 := hOperation
      · rw [dif_neg hArgs] at hEval
        cases hEval

/-- Lemma 3.4 in the many-sorted setting: if total encoded evaluation marks a
term as defined, evaluation in the `beta` reduct produces that value. -/
theorem term_evalPartial_complete
    {Sigma : Signature.{u}}
    {Var : Sigma.SortId -> Type x}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (rho : Assignment Sigma Var (beta M hM).Carrier)
    {s : Sigma.SortId}
    (term : Term Sigma Var s)
    (hDefined : M.existenceEq s
      (term.evalEncoded M (liftBetaAssignment hM rho))
      (term.evalEncoded M (liftBetaAssignment hM rho)) = M.trueValue) :
    term.evalPartial (beta M hM) rho =
      some ⟨term.evalEncoded M (liftBetaAssignment hM rho), hDefined⟩ := by
  induction term with
  | var name =>
      change some (rho _ name) =
        some ⟨(rho _ name).1, hDefined⟩
      congr 1
  | total f args ih =>
      let encodedArgs := fun i =>
        Term.evalEncoded M (liftBetaAssignment hM rho) (args i)
      have hArgDefined : AllDefinedTotal M f encodedArgs :=
        hM.total_reflects_defined f encodedArgs hDefined
      let canonical := fun i =>
        (⟨encodedArgs i, hArgDefined i⟩ :
          (beta M hM).Carrier (Sigma.totalArgSort f i))
      have hEach : forall i,
          Term.evalPartial (beta M hM) rho (args i) = some (canonical i) := by
        intro i
        exact ih i (hArgDefined i)
      have hAll : AllSome
          (fun i => Term.evalPartial (beta M hM) rho (args i)) := by
        intro i
        exact ⟨canonical i, hEach i⟩
      change (if h : AllSome
          (fun i => Term.evalPartial (beta M hM) rho (args i)) then
          some ((beta M hM).evalTotal f (fun i => someValue h i))
        else none) = _
      rw [dif_pos hAll]
      congr 1
      apply Subtype.ext
      change M.evalTotal f (fun i => (someValue hAll i).1) =
        M.evalTotal f encodedArgs
      apply congrArg (M.evalTotal f)
      funext i
      have hSelected := someValue_spec hAll i
      rw [hEach i] at hSelected
      exact congrArg Subtype.val (Option.some.inj hSelected).symm
  | partialApp f args ih =>
      let encodedArgs := fun i =>
        Term.evalEncoded M (liftBetaAssignment hM rho) (args i)
      have hArgDefined : AllDefinedPartial M f encodedArgs :=
        hM.partial_reflects_defined f encodedArgs hDefined
      let canonical := fun i =>
        (⟨encodedArgs i, hArgDefined i⟩ :
          (beta M hM).Carrier (Sigma.partialArgSort f i))
      have hEach : forall i,
          Term.evalPartial (beta M hM) rho (args i) = some (canonical i) := by
        intro i
        exact ih i (hArgDefined i)
      have hAll : AllSome
          (fun i => Term.evalPartial (beta M hM) rho (args i)) := by
        intro i
        exact ⟨canonical i, hEach i⟩
      change (if h : AllSome
          (fun i => Term.evalPartial (beta M hM) rho (args i)) then
          (beta M hM).evalPartial f (fun i => someValue h i)
        else none) = _
      rw [dif_pos hAll]
      apply (beta_partial_eq_some_iff M hM f
        (fun i => someValue hAll i)
        ⟨M.evalPartialSymbol f encodedArgs, hDefined⟩).2
      apply congrArg (M.evalPartialSymbol f)
      funext i
      have hSelected := someValue_spec hAll i
      rw [hEach i] at hSelected
      exact congrArg Subtype.val (Option.some.inj hSelected).symm

/-- Lifting a `beta` assignment commutes with adjoining one bound variable. -/
theorem liftBetaAssignment_extend
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    (hM : SatisfiesGamma M)
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma (beta M hM).Carrier context)
    {s : Sigma.SortId}
    (value : (beta M hM).Carrier s) :
    liftBetaAssignment hM (ContextAssignment.extend rho value) =
      ContextAssignment.extend (liftBetaAssignment hM rho) value.1 := by
  funext t name
  cases name with
  | here => rfl
  | there name => rfl

/-- Diaconescu's satisfaction condition for `alpha` and `beta`, for
many-sorted signatures with arbitrary finite arities and distinct `TF/PF`
operation families. -/
theorem alpha_satisfaction_condition
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma (beta M hM).Carrier context)
    (formula : Formula Sigma context) :
    formula.Sat (beta M hM) rho <->
      (alpha formula).Sat M (liftBetaAssignment hM rho) := by
  induction formula with
  | existenceEquality left right =>
      change
        (Exists fun value =>
          left.evalPartial (beta M hM) rho = some value /\
            right.evalPartial (beta M hM) rho = some value) <->
        M.existenceEq _
          (left.evalEncoded M (liftBetaAssignment hM rho))
          (right.evalEncoded M (liftBetaAssignment hM rho)) = M.trueValue
      constructor
      · rintro ⟨value, hLeft, hRight⟩
        have hLeftValue :=
          term_evalPartial_sound M hM rho left value hLeft
        have hRightValue :=
          term_evalPartial_sound M hM rho right value hRight
        rw [hLeftValue, hRightValue]
        exact value.property
      · intro hEquality
        let leftValue := left.evalEncoded M (liftBetaAssignment hM rho)
        let rightValue := right.evalEncoded M (liftBetaAssignment hM rho)
        have hLeftDefined :
            M.existenceEq _ leftValue leftValue = M.trueValue :=
          hM.equality_defined_left _ leftValue rightValue hEquality
        have hValuesEqual : leftValue = rightValue :=
          hM.equality_sound _ leftValue rightValue hEquality
        have hRightDefined :
            M.existenceEq _ rightValue rightValue = M.trueValue := by
          simpa [hValuesEqual] using hLeftDefined
        let value : (beta M hM).Carrier _ :=
          ⟨leftValue, hLeftDefined⟩
        refine ⟨value, ?_, ?_⟩
        · exact term_evalPartial_complete M hM rho left hLeftDefined
        · have hRightEval :=
            term_evalPartial_complete M hM rho right hRightDefined
          have hSubtype :
              (⟨rightValue, hRightDefined⟩ : (beta M hM).Carrier _) =
                value := by
            apply Subtype.ext
            exact hValuesEqual.symm
          exact hRightEval.trans (congrArg Option.some hSubtype)
  | conjunction left right ihLeft ihRight =>
      change
        (left.Sat (beta M hM) rho /\ right.Sat (beta M hM) rho) <->
          (alpha left).Sat M (liftBetaAssignment hM rho) /\
            (alpha right).Sat M (liftBetaAssignment hM rho)
      exact and_congr (ihLeft rho) (ihRight rho)
  | negation body ih =>
      change
        Not (body.Sat (beta M hM) rho) <->
          Not ((alpha body).Sat M (liftBetaAssignment hM rho))
      exact not_congr (ih rho)
  | universal s body ih =>
      change
        (forall value : (beta M hM).Carrier s,
          body.Sat (beta M hM) (ContextAssignment.extend rho value)) <->
        (forall value : M.Data s,
          M.existenceEq s value value = M.trueValue ->
            (alpha body).Sat M
              (ContextAssignment.extend
                (liftBetaAssignment hM rho) value))
      constructor
      · intro hPartial value hDefined
        let definedValue : (beta M hM).Carrier s := ⟨value, hDefined⟩
        have hBodyPartial := hPartial definedValue
        have hBodyEncoded :=
          (ih (ContextAssignment.extend rho definedValue)).1 hBodyPartial
        rw [liftBetaAssignment_extend hM rho definedValue] at hBodyEncoded
        exact hBodyEncoded
      · intro hEncoded definedValue
        apply (ih (ContextAssignment.extend rho definedValue)).2
        have hBodyEncoded := hEncoded definedValue.1 definedValue.property
        rw [liftBetaAssignment_extend hM rho definedValue]
        exact hBodyEncoded

/-!
## The many-sorted free total completion

The following normal forms retain an old value whenever an operation is
already defined in the source partial algebra.  All other applications are
kept as formal suspensions.  This is the finite-arity, many-sorted analogue
of the free Resolution completion used by the binary core.
-/

namespace Free

inductive RawAnswer
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) : Sigma.SortId -> Type (max u v) where
  | old {s : Sigma.SortId} (value : D.Carrier s) : RawAnswer D s
  | totalSusp (f : Sigma.TotalOp)
      (args : forall i : Fin (Sigma.totalArity f),
        RawAnswer D (Sigma.totalArgSort f i)) :
      RawAnswer D (Sigma.totalResultSort f)
  | partialSusp (f : Sigma.PartialOp)
      (args : forall i : Fin (Sigma.partialArity f),
        RawAnswer D (Sigma.partialArgSort f i)) :
      RawAnswer D (Sigma.partialResultSort f)

def AllOld
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {n : Nat}
    {sorts : Fin n -> Sigma.SortId}
    (args : forall i, RawAnswer D (sorts i)) : Prop :=
  forall i, Exists fun value : D.Carrier (sorts i) =>
    args i = .old value

noncomputable def oldValue
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {n : Nat}
    {sorts : Fin n -> Sigma.SortId}
    {args : forall i, RawAnswer D (sorts i)}
    (h : AllOld args)
    (i : Fin n) : D.Carrier (sorts i) :=
  Classical.choose (h i)

theorem oldValue_spec
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {n : Nat}
    {sorts : Fin n -> Sigma.SortId}
    {args : forall i, RawAnswer D (sorts i)}
    (h : AllOld args)
    (i : Fin n) :
    args i = .old (oldValue h i) :=
  Classical.choose_spec (h i)

noncomputable def liftTotal
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : forall i : Fin (Sigma.totalArity f),
      RawAnswer D (Sigma.totalArgSort f i)) :
    RawAnswer D (Sigma.totalResultSort f) :=
  if h : AllOld args then
    .old (D.evalTotal f (fun i => oldValue h i))
  else
    .totalSusp f args

noncomputable def liftPartial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : forall i : Fin (Sigma.partialArity f),
      RawAnswer D (Sigma.partialArgSort f i)) :
    RawAnswer D (Sigma.partialResultSort f) :=
  if h : AllOld args then
    match D.evalPartial f (fun i => oldValue h i) with
    | some result => .old result
    | none => .partialSusp f args
  else
    .partialSusp f args

@[simp] theorem liftTotal_old
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma D.Carrier f) :
    liftTotal D f (fun i => .old (args i)) =
      .old (D.evalTotal f args) := by
  let rawArgs := fun i =>
    (RawAnswer.old (D := D) (args i) :
      RawAnswer D (Sigma.totalArgSort f i))
  have hOld : AllOld rawArgs := fun i => ⟨args i, rfl⟩
  rw [liftTotal, dif_pos hOld]
  apply congrArg RawAnswer.old
  apply congrArg (D.evalTotal f)
  funext i
  exact RawAnswer.old.inj (oldValue_spec hOld i).symm

@[simp] theorem liftPartial_old_of_some
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma D.Carrier f)
    (result : D.Carrier (Sigma.partialResultSort f))
    (hEval : D.evalPartial f args = some result) :
    liftPartial D f (fun i => .old (args i)) = .old result := by
  let rawArgs := fun i =>
    (RawAnswer.old (D := D) (args i) :
      RawAnswer D (Sigma.partialArgSort f i))
  have hOld : AllOld rawArgs := fun i => ⟨args i, rfl⟩
  rw [liftPartial, dif_pos hOld]
  have hValues : (fun i => oldValue hOld i) = args := by
    funext i
    exact RawAnswer.old.inj (oldValue_spec hOld i).symm
  rw [hValues, hEval]

@[simp] theorem liftPartial_old_of_none
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma D.Carrier f)
    (hEval : D.evalPartial f args = none) :
    liftPartial D f (fun i => .old (args i)) =
      .partialSusp f (fun i => .old (args i)) := by
  let rawArgs := fun i =>
    (RawAnswer.old (D := D) (args i) :
      RawAnswer D (Sigma.partialArgSort f i))
  have hOld : AllOld rawArgs := fun i => ⟨args i, rfl⟩
  rw [liftPartial, dif_pos hOld]
  have hValues : (fun i => oldValue hOld i) = args := by
    funext i
    exact RawAnswer.old.inj (oldValue_spec hOld i).symm
  rw [hValues, hEval]

theorem liftTotal_eq_old_inputs
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : forall i : Fin (Sigma.totalArity f),
      RawAnswer D (Sigma.totalArgSort f i))
    {result : D.Carrier (Sigma.totalResultSort f)}
    (hResult : liftTotal D f args = .old result) :
    AllOld args := by
  by_cases hOld : AllOld args
  · exact hOld
  · simp [liftTotal, hOld] at hResult

theorem liftPartial_eq_old_inputs
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : forall i : Fin (Sigma.partialArity f),
      RawAnswer D (Sigma.partialArgSort f i))
    {result : D.Carrier (Sigma.partialResultSort f)}
    (hResult : liftPartial D f args = .old result) :
    AllOld args := by
  by_cases hOld : AllOld args
  · exact hOld
  · simp [liftPartial, hOld] at hResult

noncomputable def resolve
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    {s : Sigma.SortId} -> Term Sigma D.Carrier s -> RawAnswer D s
  | _, .var value => .old value
  | _, .total f args =>
      liftTotal D f (fun i => resolve D (args i))
  | _, .partialApp f args =>
      liftPartial D f (fun i => resolve D (args i))

abbrev Generated
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId) :=
  {answer : RawAnswer D s //
    Exists fun term : Term Sigma D.Carrier s => resolve D term = answer}

noncomputable def generatedTerm
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    {s : Sigma.SortId}
    (term : Term Sigma D.Carrier s) : Generated D s :=
  ⟨resolve D term, ⟨term, rfl⟩⟩

noncomputable def generatedOld
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    {s : Sigma.SortId}
    (value : D.Carrier s) : Generated D s :=
  generatedTerm D (.var value)

noncomputable def witness
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {s : Sigma.SortId}
    (answer : Generated D s) : Term Sigma D.Carrier s :=
  Classical.choose answer.property

theorem witness_spec
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {s : Sigma.SortId}
    (answer : Generated D s) :
    resolve D (witness answer) = answer.1 :=
  Classical.choose_spec answer.property

noncomputable def generatedTotal
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma (Generated D) f) :
    Generated D (Sigma.totalResultSort f) :=
  ⟨liftTotal D f (fun i => (args i).1),
    ⟨.total f (fun i => witness (args i)), by
      change liftTotal D f (fun i => resolve D (witness (args i))) =
        liftTotal D f (fun i => (args i).1)
      apply congrArg (liftTotal D f)
      funext i
      exact witness_spec (args i)⟩⟩

noncomputable def generatedPartial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (Generated D) f) :
    Generated D (Sigma.partialResultSort f) :=
  ⟨liftPartial D f (fun i => (args i).1),
    ⟨.partialApp f (fun i => witness (args i)), by
      change liftPartial D f (fun i => resolve D (witness (args i))) =
        liftPartial D f (fun i => (args i).1)
      apply congrArg (liftPartial D f)
      funext i
      exact witness_spec (args i)⟩⟩

theorem generatedOld_injective
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId) :
    Function.Injective (generatedOld D (s := s)) := by
  intro a b h
  have hValue := congrArg Subtype.val h
  exact RawAnswer.old.inj hValue

@[simp] theorem generatedTotal_old
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma D.Carrier f) :
    generatedTotal D f (fun i => generatedOld D (args i)) =
      generatedOld D (D.evalTotal f args) := by
  apply Subtype.ext
  exact liftTotal_old D f args

@[simp] theorem generatedPartial_old_of_some
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma D.Carrier f)
    (result : D.Carrier (Sigma.partialResultSort f))
    (hEval : D.evalPartial f args = some result) :
    generatedPartial D f (fun i => generatedOld D (args i)) =
      generatedOld D result := by
  apply Subtype.ext
  exact liftPartial_old_of_some D f args result hEval

theorem generatedTotal_eq_old_inputs
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma (Generated D) f)
    {result : D.Carrier (Sigma.totalResultSort f)}
    (hResult : generatedTotal D f args = generatedOld D result) :
    forall i, Exists fun value : D.Carrier (Sigma.totalArgSort f i) =>
      args i = generatedOld D value := by
  have hRaw := liftTotal_eq_old_inputs D f (fun i => (args i).1)
    (congrArg Subtype.val hResult)
  intro i
  rcases hRaw i with ⟨value, hValue⟩
  exact ⟨value, Subtype.ext hValue⟩

theorem generatedPartial_eq_old_inputs
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (Generated D) f)
    {result : D.Carrier (Sigma.partialResultSort f)}
    (hResult : generatedPartial D f args = generatedOld D result) :
    forall i, Exists fun value : D.Carrier (Sigma.partialArgSort f i) =>
      args i = generatedOld D value := by
  have hRaw := liftPartial_eq_old_inputs D f (fun i => (args i).1)
    (congrArg Subtype.val hResult)
  intro i
  rcases hRaw i with ⟨value, hValue⟩
  exact ⟨value, Subtype.ext hValue⟩

set_option linter.checkUnivs false in
structure CompatibleAlg
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) where
  Carrier : Sigma.SortId -> Type x
  embed : forall s, D.Carrier s -> Carrier s
  evalTotal : forall f : Sigma.TotalOp,
    TotalArgs Sigma Carrier f -> Carrier (Sigma.totalResultSort f)
  evalPartialSymbol : forall f : Sigma.PartialOp,
    PartialArgs Sigma Carrier f -> Carrier (Sigma.partialResultSort f)
  preserve_total : forall (f : Sigma.TotalOp)
      (args : TotalArgs Sigma D.Carrier f),
    evalTotal f (fun i => embed _ (args i)) =
      embed _ (D.evalTotal f args)
  preserve_partial : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma D.Carrier f)
      (result : D.Carrier (Sigma.partialResultSort f)),
    D.evalPartial f args = some result ->
      evalPartialSymbol f (fun i => embed _ (args i)) = embed _ result

noncomputable def CompatibleAlg.interpRaw
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D) :
    {s : Sigma.SortId} -> RawAnswer D s -> C.Carrier s
  | _, .old value => C.embed _ value
  | _, .totalSusp f args =>
      C.evalTotal f (fun i => interpRaw C (args i))
  | _, .partialSusp f args =>
      C.evalPartialSymbol f (fun i => interpRaw C (args i))

private theorem interpRaw_oldValue
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    {n : Nat}
    {sorts : Fin n -> Sigma.SortId}
    {args : forall i, RawAnswer D (sorts i)}
    (hOld : AllOld args) :
    (fun i => C.interpRaw (args i)) =
      (fun i => C.embed _ (oldValue hOld i)) := by
  funext i
  rw [oldValue_spec hOld i]
  rfl

theorem CompatibleAlg.interp_liftTotal
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    (f : Sigma.TotalOp)
    (args : forall i : Fin (Sigma.totalArity f),
      RawAnswer D (Sigma.totalArgSort f i)) :
    C.interpRaw (liftTotal D f args) =
      C.evalTotal f (fun i => C.interpRaw (args i)) := by
  by_cases hOld : AllOld args
  · rw [liftTotal, dif_pos hOld]
    change C.embed _ (D.evalTotal f (fun i => oldValue hOld i)) = _
    rw [<- C.preserve_total f (fun i => oldValue hOld i)]
    exact congrArg (C.evalTotal f) (interpRaw_oldValue C hOld).symm
  · rw [liftTotal, dif_neg hOld]
    rfl

theorem CompatibleAlg.interp_liftPartial
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    (f : Sigma.PartialOp)
    (args : forall i : Fin (Sigma.partialArity f),
      RawAnswer D (Sigma.partialArgSort f i)) :
    C.interpRaw (liftPartial D f args) =
      C.evalPartialSymbol f (fun i => C.interpRaw (args i)) := by
  by_cases hOld : AllOld args
  · rw [liftPartial, dif_pos hOld]
    cases hEval : D.evalPartial f (fun i => oldValue hOld i) with
    | none =>
        rfl
    | some result =>
        change C.embed _ result = _
        rw [<- C.preserve_partial f (fun i => oldValue hOld i) result hEval]
        exact congrArg (C.evalPartialSymbol f)
          (interpRaw_oldValue C hOld).symm
  · rw [liftPartial, dif_neg hOld]
    rfl

noncomputable def CompatibleAlg.interp
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D) :
    forall s, Generated D s -> C.Carrier s :=
  fun _ answer => C.interpRaw answer.1

@[simp] theorem CompatibleAlg.interp_generatedOld
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    {s : Sigma.SortId}
    (value : D.Carrier s) :
    C.interp _ (generatedOld D value) = C.embed s value := rfl

theorem CompatibleAlg.interp_generatedTotal
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma (Generated D) f) :
    C.interp _ (generatedTotal D f args) =
      C.evalTotal f (fun i => C.interp _ (args i)) :=
  C.interp_liftTotal f (fun i => (args i).1)

theorem CompatibleAlg.interp_generatedPartial
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (Generated D) f) :
    C.interp _ (generatedPartial D f args) =
      C.evalPartialSymbol f (fun i => C.interp _ (args i)) :=
  C.interp_liftPartial f (fun i => (args i).1)

structure CompatibleHom
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    (C : CompatibleAlg.{u,v,x} D) where
  toFun : forall s, Generated D s -> C.Carrier s
  map_old : forall (s : Sigma.SortId) (value : D.Carrier s),
    toFun s (generatedOld D value) = C.embed s value
  map_total : forall (f : Sigma.TotalOp)
      (args : TotalArgs Sigma (Generated D) f),
    toFun _ (generatedTotal D f args) =
      C.evalTotal f (fun i => toFun _ (args i))
  map_partial : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma (Generated D) f),
    toFun _ (generatedPartial D f args) =
      C.evalPartialSymbol f (fun i => toFun _ (args i))

private theorem generatedTerm_total
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : forall i : Fin (Sigma.totalArity f),
      Term Sigma D.Carrier (Sigma.totalArgSort f i)) :
    generatedTerm D (.total f args) =
      generatedTotal D f (fun i => generatedTerm D (args i)) := by
  apply Subtype.ext
  rfl

private theorem generatedTerm_partial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : forall i : Fin (Sigma.partialArity f),
      Term Sigma D.Carrier (Sigma.partialArgSort f i)) :
    generatedTerm D (.partialApp f args) =
      generatedPartial D f (fun i => generatedTerm D (args i)) := by
  apply Subtype.ext
  rfl

private theorem CompatibleHom.on_generatedTerm
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {C : CompatibleAlg.{u,v,x} D}
    (H : CompatibleHom C)
    {s : Sigma.SortId}
    (term : Term Sigma D.Carrier s) :
    H.toFun s (generatedTerm D term) = C.interp s (generatedTerm D term) := by
  induction term with
  | var value =>
      exact H.map_old _ value
  | total f args ih =>
      rw [generatedTerm_total D f args, H.map_total,
        C.interp_generatedTotal]
      exact congrArg (C.evalTotal f) (funext ih)
  | partialApp f args ih =>
      rw [generatedTerm_partial D f args, H.map_partial,
        C.interp_generatedPartial]
      exact congrArg (C.evalPartialSymbol f) (funext ih)

theorem compatibleHom_unique
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {C : CompatibleAlg.{u,v,x} D}
    (H : CompatibleHom C) : H.toFun = C.interp := by
  funext s answer
  let term := witness answer
  have hAnswer : answer = generatedTerm D term := by
    apply Subtype.ext
    exact (witness_spec answer).symm
  rw [hAnswer]
  exact H.on_generatedTerm term

end Free

/-!
## The canonical encoded algebra `gamma D`
-/

/-- Two generated elements are the same diagonal occurrence of an old,
defined element. -/
def SameOld
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    {s : Sigma.SortId}
    (left right : Free.Generated D s) : Prop :=
  Exists fun value : D.Carrier s =>
    left = Free.generatedOld D value /\
      right = Free.generatedOld D value

/-- A sorted pair outside the old diagonal. -/
structure Failure
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) where
  sort : Sigma.SortId
  left : Free.Generated D sort
  right : Free.Generated D sort
  not_same_old : Not (SameOld D left right)

/-- The auxiliary truth carrier has one distinguished true point and a
separate witness for every failed existence equality. -/
inductive GammaTruth
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) : Type (max u v) where
  | trueValue
  | failure (witness : Failure D)

noncomputable def gammaExistenceEq
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId)
    (left right : Free.Generated D s) : GammaTruth D :=
  if h : SameOld D left right then
    .trueValue
  else
    .failure ⟨s, left, right, h⟩

theorem gammaExistenceEq_eq_true_iff
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId)
    (left right : Free.Generated D s) :
    gammaExistenceEq D s left right = GammaTruth.trueValue <->
      SameOld D left right := by
  by_cases hSame : SameOld D left right
  · simp [gammaExistenceEq, hSame]
  · simp [gammaExistenceEq, hSame]

@[simp] theorem gammaExistenceEq_failure
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (failure : Failure D) :
    gammaExistenceEq D failure.sort failure.left failure.right =
      GammaTruth.failure failure := by
  cases failure with
  | mk sort left right hNot =>
      simp [gammaExistenceEq, hNot]

/-- The finite-arity many-sorted canonical total encoding. -/
noncomputable def gamma
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    EncodedAlg.{u, max u v, max u v} Sigma where
  Data := Free.Generated D
  Truth := GammaTruth D
  evalTotal := Free.generatedTotal D
  evalPartialSymbol := Free.generatedPartial D
  existenceEq := gammaExistenceEq D
  trueValue := GammaTruth.trueValue

/-- The canonical encoding satisfies every clause of `Gamma`, including the
preservation/reflection clauses for `TF` and the reflection clause for
`PF`. -/
theorem gamma_satisfiesGamma
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) : SatisfiesGamma (gamma D) := by
  constructor
  · intro f args hArgs
    have hSame : forall i, SameOld D (args i) (args i) := fun i =>
      (gammaExistenceEq_eq_true_iff D _ (args i) (args i)).1 (hArgs i)
    let oldArgs := fun i => Classical.choose (hSame i)
    have hArgEq : forall i, args i = Free.generatedOld D (oldArgs i) :=
      fun i => (Classical.choose_spec (hSame i)).1
    apply (gammaExistenceEq_eq_true_iff D _ _ _).2
    refine ⟨D.evalTotal f oldArgs, ?_, ?_⟩
    · rw [show args = (fun i => Free.generatedOld D (oldArgs i)) from
          funext hArgEq]
      exact Free.generatedTotal_old D f oldArgs
    · rw [show args = (fun i => Free.generatedOld D (oldArgs i)) from
          funext hArgEq]
      exact Free.generatedTotal_old D f oldArgs
  · intro s left right hEquality
    apply (gammaExistenceEq_eq_true_iff D s left left).2
    rcases (gammaExistenceEq_eq_true_iff D s left right).1 hEquality with
      ⟨value, hLeft, hRight⟩
    exact ⟨value, hLeft, hLeft⟩
  · intro s left right hEquality
    rcases (gammaExistenceEq_eq_true_iff D s left right).1 hEquality with
      ⟨value, hLeft, hRight⟩
    exact hLeft.trans hRight.symm
  · intro f args hResult
    rcases (gammaExistenceEq_eq_true_iff D _ _ _).1 hResult with
      ⟨result, hOld, _⟩
    have hInputs := Free.generatedTotal_eq_old_inputs D f args hOld
    intro i
    rcases hInputs i with ⟨value, hValue⟩
    apply (gammaExistenceEq_eq_true_iff D _ (args i) (args i)).2
    exact ⟨value, hValue, hValue⟩
  · intro f args hResult
    rcases (gammaExistenceEq_eq_true_iff D _ _ _).1 hResult with
      ⟨result, hOld, _⟩
    have hInputs := Free.generatedPartial_eq_old_inputs D f args hOld
    intro i
    rcases hInputs i with ⟨value, hValue⟩
    apply (gammaExistenceEq_eq_true_iff D _ (args i) (args i)).2
    exact ⟨value, hValue, hValue⟩

/-- Embed the old carrier into the defined part of `gamma D`, at every
sort. -/
noncomputable def betaGammaEmbed
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    forall s, D.Carrier s ->
      (beta (gamma D) (gamma_satisfiesGamma D)).Carrier s :=
  fun s value =>
    ⟨Free.generatedOld D value,
      (gammaExistenceEq_eq_true_iff D s _ _).2
        ⟨value, rfl, rfl⟩⟩

theorem betaGammaEmbed_injective
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId) :
    Function.Injective (betaGammaEmbed D s) := by
  intro left right hEqual
  apply Free.generatedOld_injective D s
  exact congrArg Subtype.val hEqual

theorem betaGammaEmbed_surjective
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId) :
    Function.Surjective (betaGammaEmbed D s) := by
  intro answer
  rcases (gammaExistenceEq_eq_true_iff D s answer.1 answer.1).1
      answer.property with ⟨value, hValue, _⟩
  refine ⟨value, ?_⟩
  apply Subtype.ext
  exact hValue.symm

/-- A sort-indexed carrier equivalence. -/
structure SortedCarrierEquiv
    {Sigma : Signature.{u}}
    (A : Sigma.SortId -> Type v)
    (B : Sigma.SortId -> Type w) where
  toFun : forall s, A s -> B s
  invFun : forall s, B s -> A s
  left_inv : forall (s : Sigma.SortId) (value : A s),
    invFun s (toFun s value) = value
  right_inv : forall (s : Sigma.SortId) (value : B s),
    toFun s (invFun s value) = value

namespace SortedCarrierEquiv

noncomputable def ofBijective
    {Sigma : Signature.{u}}
    {A : Sigma.SortId -> Type v}
    {B : Sigma.SortId -> Type w}
    (map : forall s, A s -> B s)
    (hMap : forall s, Function.Injective (map s) /\
      Function.Surjective (map s)) : SortedCarrierEquiv A B where
  toFun := map
  invFun := fun s value => Classical.choose ((hMap s).2 value)
  left_inv := by
    intro s value
    apply (hMap s).1
    exact Classical.choose_spec ((hMap s).2 (map s value))
  right_inv := by
    intro s value
    exact Classical.choose_spec ((hMap s).2 value)

end SortedCarrierEquiv

theorem betaGamma_evalTotal
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma D.Carrier f) :
    (beta (gamma D) (gamma_satisfiesGamma D)).evalTotal f
        (fun i => betaGammaEmbed D _ (args i)) =
      betaGammaEmbed D _ (D.evalTotal f args) := by
  apply Subtype.ext
  exact Free.generatedTotal_old D f args

theorem betaGamma_evalPartial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma D.Carrier f) :
    (beta (gamma D) (gamma_satisfiesGamma D)).evalPartial f
        (fun i => betaGammaEmbed D _ (args i)) =
      Option.map (betaGammaEmbed D _) (D.evalPartial f args) := by
  cases hEval : D.evalPartial f args with
  | some result =>
      apply (beta_partial_eq_some_iff (gamma D) (gamma_satisfiesGamma D)
        f (fun i => betaGammaEmbed D _ (args i))
        (betaGammaEmbed D _ result)).2
      exact Free.generatedPartial_old_of_some D f args result hEval
  | none =>
      apply (beta_partial_eq_none_iff (gamma D) (gamma_satisfiesGamma D)
        f (fun i => betaGammaEmbed D _ (args i))).2
      intro hDefined
      have hSame := (gammaExistenceEq_eq_true_iff D _ _ _).1 hDefined
      rcases hSame with ⟨result, hOld, _⟩
      have hRaw := congrArg Subtype.val hOld
      change Free.liftPartial D f (fun i => .old (args i)) =
        .old result at hRaw
      rw [Free.liftPartial_old_of_none D f args hEval] at hRaw
      cases hRaw

/-- Equivalence of many-sorted partial algebras. -/
structure PartialAlgEquiv
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (E : PartialAlg.{u,w} Sigma) where
  carrierEquiv : SortedCarrierEquiv D.Carrier E.Carrier
  map_total : forall (f : Sigma.TotalOp)
      (args : TotalArgs Sigma D.Carrier f),
    E.evalTotal f (fun i => carrierEquiv.toFun _ (args i)) =
      carrierEquiv.toFun _ (D.evalTotal f args)
  map_partial : forall (f : Sigma.PartialOp)
      (args : PartialArgs Sigma D.Carrier f),
    E.evalPartial f (fun i => carrierEquiv.toFun _ (args i)) =
      Option.map (carrierEquiv.toFun _) (D.evalPartial f args)

/-- `beta (gamma D)` recovers `D`, with all sorts, all finite arities, and
both `TF/PF` operation families respected. -/
noncomputable def betaGammaPartialAlgEquiv
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    PartialAlgEquiv D (beta (gamma D) (gamma_satisfiesGamma D)) where
  carrierEquiv := SortedCarrierEquiv.ofBijective (betaGammaEmbed D)
    (fun s => ⟨betaGammaEmbed_injective D s,
      betaGammaEmbed_surjective D s⟩)
  map_total := betaGamma_evalTotal D
  map_partial := betaGamma_evalPartial D

/-!
## Persistent liberality
-/

private noncomputable def compatibleTarget
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) : Free.CompatibleAlg.{u,v,x} D where
  Carrier := M.Data
  embed := fun s value => (hom.toFun s value).1
  evalTotal := M.evalTotal
  evalPartialSymbol := M.evalPartialSymbol
  preserve_total := by
    intro f args
    exact (congrArg Subtype.val (hom.map_total f args)).symm
  preserve_partial := by
    intro f args result hEval
    exact (beta_partial_eq_some_iff M hM f
      (fun i => hom.toFun _ (args i)) (hom.toFun _ result)).1
        (hom.map_partial f args result hEval)

private noncomputable def liftData
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) :
    forall s, Free.Generated D s -> M.Data s :=
  (compatibleTarget D M hM hom).interp

@[simp] private theorem liftData_old
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM))
    (s : Sigma.SortId)
    (value : D.Carrier s) :
    liftData D M hM hom s (Free.generatedOld D value) =
      (hom.toFun s value).1 :=
  Free.CompatibleAlg.interp_generatedOld
    (compatibleTarget D M hM hom) value

private theorem liftData_total
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM))
    (f : Sigma.TotalOp)
    (args : TotalArgs Sigma (Free.Generated D) f) :
    liftData D M hM hom _ (Free.generatedTotal D f args) =
      M.evalTotal f (fun i => liftData D M hM hom _ (args i)) :=
  Free.CompatibleAlg.interp_generatedTotal
    (compatibleTarget D M hM hom) f args

private theorem liftData_partial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM))
    (f : Sigma.PartialOp)
    (args : PartialArgs Sigma (Free.Generated D) f) :
    liftData D M hM hom _ (Free.generatedPartial D f args) =
      M.evalPartialSymbol f
        (fun i => liftData D M hM hom _ (args i)) :=
  Free.CompatibleAlg.interp_generatedPartial
    (compatibleTarget D M hM hom) f args

private noncomputable def liftTruth
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) : GammaTruth D -> M.Truth
  | .trueValue => M.trueValue
  | .failure failure =>
      M.existenceEq failure.sort
        (liftData D M hM hom failure.sort failure.left)
        (liftData D M hM hom failure.sort failure.right)

/-- The canonical total-algebra lift extending a partial homomorphism into
the `beta` reduct. -/
noncomputable def gammaLift
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) : EncodedHom (gamma D) M where
  dataMap := liftData D M hM hom
  truthMap := liftTruth D M hM hom
  map_total := liftData_total D M hM hom
  map_partial_symbol := liftData_partial D M hM hom
  map_existenceEq := by
    intro s left right
    change
      liftTruth D M hM hom (gammaExistenceEq D s left right) =
        M.existenceEq s
          (liftData D M hM hom s left)
          (liftData D M hM hom s right)
    by_cases hSame : SameOld D left right
    · rcases hSame with ⟨value, hLeft, hRight⟩
      rw [hLeft, hRight]
      rw [(gammaExistenceEq_eq_true_iff D s _ _).2
        ⟨value, rfl, rfl⟩]
      change M.trueValue = M.existenceEq s
        (liftData D M hM hom s (Free.generatedOld D value))
        (liftData D M hM hom s (Free.generatedOld D value))
      simpa using (hom.toFun s value).property.symm
    · simp [gammaExistenceEq, hSame, liftTruth]
  map_true := rfl

theorem gammaLift_agrees
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM))
    (s : Sigma.SortId)
    (value : D.Carrier s) :
    betaMap (gammaLift D M hM hom) s (betaGammaEmbed D s value) =
      hom.toFun s value := by
  apply Subtype.ext
  exact liftData_old D M hM hom s value

private noncomputable def compatibleHomOfEncodedHom
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM))
    (candidate : EncodedHom (gamma D) M)
    (hCandidate : forall (s : Sigma.SortId) (value : D.Carrier s),
      betaMap candidate s (betaGammaEmbed D s value) =
        hom.toFun s value) :
    Free.CompatibleHom (compatibleTarget D M hM hom) where
  toFun := candidate.dataMap
  map_old := by
    intro s value
    exact congrArg Subtype.val (hCandidate s value)
  map_total := candidate.map_total
  map_partial := candidate.map_partial_symbol

/-- Many-sorted persistent liberality: after the canonical identification
`beta (gamma D) ~= D`, every partial homomorphism `D -> beta M` extends to a
unique encoded homomorphism `gamma D -> M`. -/
theorem gamma_persistent_liberality
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) :
    Exists fun lift : EncodedHom (gamma D) M =>
      (forall (s : Sigma.SortId) (value : D.Carrier s),
        betaMap lift s (betaGammaEmbed D s value) =
          hom.toFun s value) /\
      forall candidate : EncodedHom (gamma D) M,
        (forall (s : Sigma.SortId) (value : D.Carrier s),
          betaMap candidate s (betaGammaEmbed D s value) =
            hom.toFun s value) ->
        candidate = lift := by
  refine ⟨gammaLift D M hM hom, gammaLift_agrees D M hM hom, ?_⟩
  intro candidate hCandidate
  let compatibleHom :=
    compatibleHomOfEncodedHom D M hM hom candidate hCandidate
  have hCompatible := Free.compatibleHom_unique compatibleHom
  have hData : candidate.dataMap = liftData D M hM hom := by
    exact hCompatible
  apply EncodedHom.ext hData
  funext truth
  cases truth with
  | trueValue =>
      exact candidate.map_true
  | failure failure =>
      have hMap := candidate.map_existenceEq failure.sort
        failure.left failure.right
      change candidate.truthMap
          (gammaExistenceEq D failure.sort failure.left failure.right) =
        M.existenceEq failure.sort
          (candidate.dataMap failure.sort failure.left)
          (candidate.dataMap failure.sort failure.right) at hMap
      rw [gammaExistenceEq_failure D failure] at hMap
      change candidate.truthMap (GammaTruth.failure failure) =
        liftTruth D M hM hom (GammaTruth.failure failure)
      change candidate.truthMap (GammaTruth.failure failure) =
        M.existenceEq failure.sort
          (liftData D M hM hom failure.sort failure.left)
          (liftData D M hM hom failure.sort failure.right)
      rw [hMap, hData]

end ManySorted
end Diaconescu
end Resolution
