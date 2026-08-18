import ResolutionDiaconescuEncoding
import ResolutionDiaconescuAdjunction

universe u v w x y

namespace Resolution
namespace Diaconescu
namespace BinarySpecialization

noncomputable local instance binarySpecializationClassicalPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# The binary one-sorted specialization of the many-sorted bridge

This module connects the two concrete Lean presentations used in the
repository.  A binary signature is embedded into the many-sorted language by
using one data sort, no designated-total symbols, and the original operation
symbols as partial symbols of arity two.  The resulting partial algebras,
homomorphisms, `Gamma` models, generated normal forms, and canonical `gamma`
encodings are compared with their pre-existing binary counterparts.
-/

/-! ## Binary arguments and the specialized signature -/

/-- A universe-polymorphic singleton data sort. -/
abbrev OneSort := ULift.{u} Unit

/-- The unique data sort of the specialized signature. -/
abbrev dataSort : OneSort.{u} := ULift.up ()

/-- A universe-polymorphic empty family of designated-total operations. -/
abbrev NoTotalOp := ULift.{u} Empty

/-- The canonical function on `Fin 2` with the prescribed two values. -/
def pairArgs {A : Type v} (left right : A) : Fin 2 -> A :=
  Fin.cases left (fun tail =>
    Fin.cases right (fun impossible => Fin.elim0 impossible) tail)

@[simp] theorem pairArgs_zero {A : Type v} (left right : A) :
    pairArgs left right 0 = left := rfl

@[simp] theorem pairArgs_one {A : Type v} (left right : A) :
    pairArgs left right 1 = right := rfl

theorem pairArgs_eta {A : Type v} (args : Fin 2 -> A) :
    pairArgs (args 0) (args 1) = args := by
  funext i
  exact Fin.cases rfl (fun tail =>
    Fin.cases rfl (fun impossible => Fin.elim0 impossible) tail) i

theorem map_pairArgs
    {A : Type v} {B : Type w}
    (map : A -> B) (left right : A) :
    (fun i => map (pairArgs left right i)) =
      pairArgs (map left) (map right) := by
  funext i
  exact Fin.cases rfl (fun tail =>
    Fin.cases rfl (fun impossible => Fin.elim0 impossible) tail) i

/-- View a binary one-sorted signature as a many-sorted signature with one
sort, no designated-total operations, and binary partial operations. -/
abbrev signature (Sigma : Resolution.Signature.{u}) :
    ManySorted.Signature.{u} where
  SortId := OneSort.{u}
  TotalOp := NoTotalOp.{u}
  PartialOp := Sigma.Op
  totalArity := fun operation => nomatch operation.down
  totalArgSort := fun operation => nomatch operation.down
  totalResultSort := fun operation => nomatch operation.down
  partialArity := fun _ => 2
  partialArgSort := fun _ _ => dataSort
  partialResultSort := fun _ => dataSort

/-! ## Partial algebras and homomorphisms -/

/-- Interpret a binary partial algebra in the specialized many-sorted
signature. -/
def toManySortedPartialAlg
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ManySorted.PartialAlg.{u,v} (signature Sigma) where
  Carrier := fun _ => D.Carrier
  evalTotal := fun operation => nomatch operation.down
  evalPartial := fun operation args => D.eval operation (args 0) (args 1)

/-- Forget the redundant unit sort of a partial algebra over the specialized
signature. -/
def fromManySortedPartialAlg
    {Sigma : Resolution.Signature.{u}}
    (D : ManySorted.PartialAlg.{u,v} (signature Sigma)) :
    Resolution.PartialAlg.{u,v} Sigma where
  Carrier := D.Carrier dataSort
  eval := fun operation left right =>
    D.evalPartial operation (pairArgs left right)

@[simp] theorem fromManySortedPartialAlg_toManySortedPartialAlg
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    fromManySortedPartialAlg (toManySortedPartialAlg D) = D := by
  cases D
  rfl

/-- Every partial algebra over the specialized signature is canonically
equivalent to the constant unit-sorted presentation obtained by forgetting
and restoring its unique sort. -/
noncomputable def toFromPartialAlgEquiv
    {Sigma : Resolution.Signature.{u}}
    (D : ManySorted.PartialAlg.{u,v} (signature Sigma)) :
    ManySorted.PartialAlgEquiv D
      (toManySortedPartialAlg (fromManySortedPartialAlg D)) where
  carrierEquiv :=
    { toFun := fun sort value => by
        cases sort
        exact value
      invFun := fun sort value => by
        cases sort
        exact value
      left_inv := by
        intro sort value
        cases sort
        rfl
      right_inv := by
        intro sort value
        cases sort
        rfl }
  map_total := by
    intro operation
    exact nomatch operation.down
  map_partial := by
    intro operation args
    change D.evalPartial operation (pairArgs (args 0) (args 1)) =
      Option.map (fun value => value) (D.evalPartial operation args)
    rw [pairArgs_eta]
    simp

/-- Send a binary partial homomorphism to the specialized many-sorted
presentation. -/
def toManySortedPartialHom
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    {E : Resolution.PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E) :
    ManySorted.PartialHom
      (toManySortedPartialAlg D) (toManySortedPartialAlg E) where
  toFun := fun _ => hom.toFun
  map_total := by
    intro operation
    exact nomatch operation.down
  map_partial := by
    intro operation args result hEval
    exact hom.map_defined operation (args 0) (args 1) result hEval

/-- Forget the redundant unit sort of a homomorphism over the specialized
signature. -/
def fromManySortedPartialHom
    {Sigma : Resolution.Signature.{u}}
    {D : ManySorted.PartialAlg.{u,v} (signature Sigma)}
    {E : ManySorted.PartialAlg.{u,w} (signature Sigma)}
    (hom : ManySorted.PartialHom D E) :
    PartialHom (fromManySortedPartialAlg D) (fromManySortedPartialAlg E) where
  toFun := hom.toFun dataSort
  map_defined := by
    intro operation left right result hEval
    change E.evalPartial operation
      (pairArgs (hom.toFun dataSort left) (hom.toFun dataSort right)) =
        some (hom.toFun dataSort result)
    rw [<- map_pairArgs (hom.toFun dataSort) left right]
    exact hom.map_partial operation (pairArgs left right) result hEval

@[simp] theorem fromManySortedPartialHom_toManySortedPartialHom
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    {E : Resolution.PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E) :
    fromManySortedPartialHom (toManySortedPartialHom hom) = hom := by
  apply PartialHom.ext
  rfl

/-! ## Encoded algebras and the Horn theory `Gamma` -/

/-- Interpret a binary encoded algebra in the specialized many-sorted
signature. -/
def toManySortedEncodedAlg
    {Sigma : Resolution.Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma) :
    ManySorted.EncodedAlg.{u,v,w} (signature Sigma) where
  Data := fun _ => M.Data
  Truth := M.Truth
  evalTotal := fun operation => nomatch operation.down
  evalPartialSymbol := fun operation args => M.op operation (args 0) (args 1)
  existenceEq := fun _ => M.existenceEq
  trueValue := M.trueValue

/-- Forget the redundant unit sort of an encoded algebra over the specialized
signature. -/
def fromManySortedEncodedAlg
    {Sigma : Resolution.Signature.{u}}
    (M : ManySorted.EncodedAlg.{u,v,w} (signature Sigma)) :
    EncodedAlg.{u,v,w} Sigma where
  Data := M.Data dataSort
  Truth := M.Truth
  op := fun operation left right =>
    M.evalPartialSymbol operation (pairArgs left right)
  existenceEq := M.existenceEq dataSort
  trueValue := M.trueValue

@[simp] theorem fromManySortedEncodedAlg_toManySortedEncodedAlg
    {Sigma : Resolution.Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma) :
    fromManySortedEncodedAlg (toManySortedEncodedAlg M) = M := by
  cases M
  rfl

/-- The three binary Horn clauses imply the five-field many-sorted `Gamma`
record after specialization; the total-operation fields are vacuous. -/
theorem toManySorted_satisfiesGamma
    {Sigma : Resolution.Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    (hM : SatisfiesGamma M) :
    ManySorted.SatisfiesGamma (toManySortedEncodedAlg M) where
  total_preserves_defined := by
    intro operation
    exact nomatch operation.down
  equality_defined_left := fun _ => hM.defined_left
  equality_sound := fun _ => hM.equality_sound
  total_reflects_defined := by
    intro operation
    exact nomatch operation.down
  partial_reflects_defined := by
    intro operation args hDefined
    have hInputs := hM.operation_strict operation (args 0) (args 1) hDefined
    intro i
    exact Fin.cases hInputs.1 (fun tail =>
      Fin.cases hInputs.2 (fun impossible => Fin.elim0 impossible) tail) i

/-- Conversely, a many-sorted `Gamma` proof restricts to the three binary
Horn clauses. -/
theorem fromManySorted_satisfiesGamma
    {Sigma : Resolution.Signature.{u}}
    {M : ManySorted.EncodedAlg.{u,v,w} (signature Sigma)}
    (hM : ManySorted.SatisfiesGamma M) :
    SatisfiesGamma (fromManySortedEncodedAlg M) where
  defined_left := hM.equality_defined_left dataSort
  equality_sound := hM.equality_sound dataSort
  operation_strict := by
    intro operation left right hDefined
    have hInputs := hM.partial_reflects_defined operation
      (pairArgs left right) hDefined
    exact ⟨hInputs 0, hInputs 1⟩

/-! ## Equivalence of the generated normal-form carriers -/

private noncomputable def manyGeneratedAsBinaryCompatible
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Free.CompatibleAlg.{u,v,max u v} D where
  Carrier := ManySorted.Free.Generated (toManySortedPartialAlg D) dataSort
  embed := ManySorted.Free.generatedOld (toManySortedPartialAlg D)
  op := fun operation left right =>
    ManySorted.Free.generatedPartial (toManySortedPartialAlg D) operation
      (pairArgs left right)
  preserve := by
    intro operation left right result hEval
    rw [<- map_pairArgs
      (ManySorted.Free.generatedOld (toManySortedPartialAlg D)) left right]
    exact ManySorted.Free.generatedPartial_old_of_some
      (toManySortedPartialAlg D) operation (pairArgs left right) result hEval

/-- Map a binary generated Answer into the specialized many-sorted generated
normal form by the binary universal property. -/
noncomputable def generatedToManySorted
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Free.GeneratedAns D ->
      ManySorted.Free.Generated (toManySortedPartialAlg D) dataSort :=
  Free.CompatibleAlg.interp D (manyGeneratedAsBinaryCompatible D)

@[simp] theorem generatedToManySorted_old
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (value : D.Carrier) :
    generatedToManySorted D (Free.generatedOld D value) =
      ManySorted.Free.generatedOld (toManySortedPartialAlg D) value :=
  Free.CompatibleAlg.interp_generatedOld
    D (manyGeneratedAsBinaryCompatible D) value

theorem generatedToManySorted_op
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (operation : Sigma.Op)
    (left right : Free.GeneratedAns D) :
    generatedToManySorted D (Free.generatedOp D operation left right) =
      ManySorted.Free.generatedPartial (toManySortedPartialAlg D) operation
        (pairArgs (generatedToManySorted D left)
          (generatedToManySorted D right)) :=
  Free.CompatibleAlg.interp_generatedOp
    D (manyGeneratedAsBinaryCompatible D) operation left right

private noncomputable def binaryGeneratedAsManyCompatible
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ManySorted.Free.CompatibleAlg.{u,v,max u v}
      (toManySortedPartialAlg D) where
  Carrier := fun _ => Free.GeneratedAns D
  embed := fun _ => Free.generatedOld D
  evalTotal := fun operation => nomatch operation.down
  evalPartialSymbol := fun operation args =>
    Free.generatedOp D operation (args 0) (args 1)
  preserve_total := by
    intro operation
    exact nomatch operation.down
  preserve_partial := by
    intro operation args result hEval
    exact Free.generatedOp_old_of_defined D operation
      (args 0) (args 1) result hEval

/-- Map a specialized many-sorted generated normal form back to the binary
generated Answer by the many-sorted universal property. -/
noncomputable def generatedFromManySorted
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    forall sort,
      ManySorted.Free.Generated (toManySortedPartialAlg D) sort ->
        Free.GeneratedAns D :=
  (binaryGeneratedAsManyCompatible D).interp

@[simp] theorem generatedFromManySorted_old
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (value : D.Carrier) :
    generatedFromManySorted D dataSort
        (ManySorted.Free.generatedOld (toManySortedPartialAlg D) value) =
      Free.generatedOld D value :=
  ManySorted.Free.CompatibleAlg.interp_generatedOld
    (binaryGeneratedAsManyCompatible D) value

theorem generatedFromManySorted_partial
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (operation : Sigma.Op)
    (args : Fin 2 ->
      ManySorted.Free.Generated (toManySortedPartialAlg D) dataSort) :
    generatedFromManySorted D dataSort
        (ManySorted.Free.generatedPartial (toManySortedPartialAlg D)
          operation args) =
      Free.generatedOp D operation
        (generatedFromManySorted D dataSort (args 0))
        (generatedFromManySorted D dataSort (args 1)) :=
  ManySorted.Free.CompatibleAlg.interp_generatedPartial
    (binaryGeneratedAsManyCompatible D) operation args

private noncomputable def binaryGeneratedCompatible
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Free.CompatibleAlg.{u,v,max u v} D where
  Carrier := Free.GeneratedAns D
  embed := Free.generatedOld D
  op := Free.generatedOp D
  preserve := Free.generatedOp_old_of_defined D

private noncomputable def binaryGeneratedIdentityHom
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Free.CompatibleHom D (binaryGeneratedCompatible D) where
  toFun := fun answer => answer
  map_old := by intros; rfl
  map_op := by intros; rfl

private noncomputable def binaryGeneratedRoundtripHom
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Free.CompatibleHom D (binaryGeneratedCompatible D) where
  toFun := fun answer =>
    generatedFromManySorted D dataSort (generatedToManySorted D answer)
  map_old := by
    intro value
    rw [generatedToManySorted_old, generatedFromManySorted_old]
    rfl
  map_op := by
    intro operation left right
    rw [generatedToManySorted_op, generatedFromManySorted_partial]
    rfl

/-- Translating a generated binary Answer to the many-sorted presentation and
back is the identity.  The proof uses uniqueness in the binary free-completion
universal property. -/
@[simp] theorem generatedFromManySorted_generatedToManySorted
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (answer : Free.GeneratedAns D) :
    generatedFromManySorted D dataSort (generatedToManySorted D answer) =
      answer := by
  have hRoundtrip := Free.compatibleHom_unique D
    (binaryGeneratedCompatible D) (binaryGeneratedRoundtripHom D)
  have hIdentity := Free.compatibleHom_unique D
    (binaryGeneratedCompatible D) (binaryGeneratedIdentityHom D)
  have hHom : binaryGeneratedRoundtripHom D =
      binaryGeneratedIdentityHom D := hRoundtrip.trans hIdentity.symm
  exact congrFun (congrArg Free.CompatibleHom.toFun hHom) answer

/-- Transport a specialized generated value from the distinguished singleton
sort to any (necessarily equal) sort. -/
noncomputable def generatedToManySortedAt
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (sort : OneSort.{u}) :
    Free.GeneratedAns D ->
      ManySorted.Free.Generated (toManySortedPartialAlg D) sort := by
  cases sort with
  | up singleton =>
      cases singleton
      exact generatedToManySorted D

@[simp] theorem generatedToManySortedAt_dataSort
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (answer : Free.GeneratedAns D) :
    generatedToManySortedAt D dataSort answer = generatedToManySorted D answer :=
  rfl

private noncomputable def manyGeneratedCompatible
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ManySorted.Free.CompatibleAlg.{u,v,max u v}
      (toManySortedPartialAlg D) where
  Carrier := fun sort =>
    ManySorted.Free.Generated (toManySortedPartialAlg D) sort
  embed := fun sort value =>
    ManySorted.Free.generatedOld (toManySortedPartialAlg D)
      (s := sort) value
  evalTotal := fun operation => nomatch operation.down
  evalPartialSymbol := fun operation args =>
    ManySorted.Free.generatedPartial (toManySortedPartialAlg D)
      operation args
  preserve_total := by
    intro operation
    exact nomatch operation.down
  preserve_partial := ManySorted.Free.generatedPartial_old_of_some
    (toManySortedPartialAlg D)

private noncomputable def manyGeneratedIdentityHom
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ManySorted.Free.CompatibleHom (manyGeneratedCompatible D) where
  toFun := fun _ answer => answer
  map_old := by intros; rfl
  map_total := by
    intro operation
    exact nomatch operation.down
  map_partial := by intros; rfl

private noncomputable def manyGeneratedRoundtripHom
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ManySorted.Free.CompatibleHom (manyGeneratedCompatible D) where
  toFun := fun sort answer =>
    generatedToManySortedAt D sort (generatedFromManySorted D sort answer)
  map_old := by
    intro sort value
    cases sort with
    | up singleton =>
        cases singleton
        change generatedToManySorted D
            (generatedFromManySorted D dataSort
              (ManySorted.Free.generatedOld
                (toManySortedPartialAlg D) value)) =
          ManySorted.Free.generatedOld (toManySortedPartialAlg D) value
        calc
          generatedToManySorted D
              (generatedFromManySorted D dataSort
                (ManySorted.Free.generatedOld
                  (toManySortedPartialAlg D) value)) =
              generatedToManySorted D (Free.generatedOld D value) :=
            congrArg (generatedToManySorted D)
              (generatedFromManySorted_old D value)
          _ = ManySorted.Free.generatedOld
                (toManySortedPartialAlg D) value :=
            generatedToManySorted_old D value
  map_total := by
    intro operation
    exact nomatch operation.down
  map_partial := by
    intro operation args
    rw [generatedFromManySorted_partial]
    change
      generatedToManySorted D
          (Free.generatedOp D operation
            (generatedFromManySorted D dataSort (args 0))
            (generatedFromManySorted D dataSort (args 1))) =
        ManySorted.Free.generatedPartial (toManySortedPartialAlg D) operation
          (fun i => generatedToManySorted D
            (generatedFromManySorted D dataSort (args i)))
    rw [generatedToManySorted_op]
    apply congrArg
    rw [<- map_pairArgs
      (fun answer => generatedToManySorted D
        (generatedFromManySorted D dataSort answer))
      (args 0) (args 1)]
    rw [pairArgs_eta]

/-- Translating a specialized many-sorted generated normal form to the binary
presentation and back is the identity at every singleton sort. -/
@[simp] theorem generatedToManySorted_generatedFromManySorted
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (sort : OneSort.{u})
    (answer : ManySorted.Free.Generated (toManySortedPartialAlg D) sort) :
    generatedToManySortedAt D sort
        (generatedFromManySorted D sort answer) = answer := by
  have hRoundtrip := ManySorted.Free.compatibleHom_unique
    (manyGeneratedRoundtripHom D)
  have hIdentity := ManySorted.Free.compatibleHom_unique
    (manyGeneratedIdentityHom D)
  have hFunctions : (manyGeneratedRoundtripHom D).toFun =
      (manyGeneratedIdentityHom D).toFun :=
    hRoundtrip.trans hIdentity.symm
  exact congrFun (congrFun hFunctions sort) answer

/-- The generated binary Answer carrier is canonically equivalent to the data
carrier of the specialized many-sorted free completion. -/
noncomputable def generatedEquiv
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    CarrierEquiv (Free.GeneratedAns D)
      (ManySorted.Free.Generated (toManySortedPartialAlg D) dataSort) where
  toFun := generatedToManySorted D
  invFun := generatedFromManySorted D dataSort
  left_inv := generatedFromManySorted_generatedToManySorted D
  right_inv := generatedToManySorted_generatedFromManySorted D dataSort

/-! ## Equivalence of the canonical `gamma` encodings -/

/-- The old-diagonal predicate is invariant under the generated-carrier
equivalence. -/
theorem sameOld_iff
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (left right : Free.GeneratedAns D) :
    SameOld D left right <->
      ManySorted.SameOld (toManySortedPartialAlg D)
        (generatedToManySorted D left) (generatedToManySorted D right) := by
  constructor
  · rintro ⟨value, hLeft, hRight⟩
    refine ⟨value, ?_, ?_⟩
    · calc
        generatedToManySorted D left =
            generatedToManySorted D (Free.generatedOld D value) :=
          congrArg (generatedToManySorted D) hLeft
        _ = ManySorted.Free.generatedOld
              (toManySortedPartialAlg D) value :=
          generatedToManySorted_old D value
    · calc
        generatedToManySorted D right =
            generatedToManySorted D (Free.generatedOld D value) :=
          congrArg (generatedToManySorted D) hRight
        _ = ManySorted.Free.generatedOld
              (toManySortedPartialAlg D) value :=
          generatedToManySorted_old D value
  · rintro ⟨value, hLeft, hRight⟩
    refine ⟨value, ?_, ?_⟩
    · calc
        left = generatedFromManySorted D dataSort
            (generatedToManySorted D left) :=
          (generatedFromManySorted_generatedToManySorted D left).symm
        _ = generatedFromManySorted D dataSort
            (ManySorted.Free.generatedOld
              (toManySortedPartialAlg D) value) :=
          congrArg (generatedFromManySorted D dataSort) hLeft
        _ = Free.generatedOld D value :=
          generatedFromManySorted_old D value
    · calc
        right = generatedFromManySorted D dataSort
            (generatedToManySorted D right) :=
          (generatedFromManySorted_generatedToManySorted D right).symm
        _ = generatedFromManySorted D dataSort
            (ManySorted.Free.generatedOld
              (toManySortedPartialAlg D) value) :=
          congrArg (generatedFromManySorted D dataSort) hRight
        _ = Free.generatedOld D value :=
          generatedFromManySorted_old D value

private theorem failure_ext
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    {left right : Failure D}
    (hLeft : left.left = right.left)
    (hRight : left.right = right.right) : left = right := by
  cases left
  cases right
  cases hLeft
  cases hRight
  rfl

private theorem manySortedFailure_ext
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    {left right : ManySorted.Failure (toManySortedPartialAlg D)}
    (hSort : left.sort = right.sort)
    (hLeft : HEq left.left right.left)
    (hRight : HEq left.right right.right) : left = right := by
  cases left
  cases right
  cases hSort
  cases hLeft
  cases hRight
  rfl

noncomputable def failureToManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (failure : Failure D) :
    ManySorted.Failure (toManySortedPartialAlg D) where
  sort := dataSort
  left := generatedToManySorted D failure.left
  right := generatedToManySorted D failure.right
  not_same_old := fun hSame =>
    failure.not_same_old ((sameOld_iff D failure.left failure.right).2 hSame)

noncomputable def failureFromManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (failure : ManySorted.Failure (toManySortedPartialAlg D)) :
    Failure D := by
  rcases failure with ⟨sort, left, right, hNot⟩
  cases sort with
  | up singleton =>
      cases singleton
      exact
        { left := generatedFromManySorted D dataSort left
          right := generatedFromManySorted D dataSort right
          not_same_old := by
            intro hSame
            apply hNot
            have hTransport := (sameOld_iff D
              (generatedFromManySorted D dataSort left)
              (generatedFromManySorted D dataSort right)).1 hSame
            have hLeft : generatedToManySorted D
                (generatedFromManySorted D dataSort left) = left := by
              simpa only [generatedToManySortedAt_dataSort] using
                generatedToManySorted_generatedFromManySorted
                D dataSort left
            have hRight : generatedToManySorted D
                (generatedFromManySorted D dataSort right) = right := by
              simpa only [generatedToManySortedAt_dataSort] using
                generatedToManySorted_generatedFromManySorted
                D dataSort right
            rw [hLeft, hRight] at hTransport
            exact hTransport }

@[simp] theorem failureFromManySorted_failureToManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (failure : Failure D) :
    failureFromManySorted (failureToManySorted failure) = failure := by
  cases failure with
  | mk left right hNot =>
      simp only [failureToManySorted, failureFromManySorted]
      apply failure_ext
      · exact generatedFromManySorted_generatedToManySorted D left
      · exact generatedFromManySorted_generatedToManySorted D right

@[simp] theorem failureToManySorted_failureFromManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (failure : ManySorted.Failure (toManySortedPartialAlg D)) :
    failureToManySorted (failureFromManySorted failure) = failure := by
  rcases failure with ⟨sort, left, right, hNot⟩
  cases sort with
  | up singleton =>
      cases singleton
      simp only [failureFromManySorted, failureToManySorted]
      apply manySortedFailure_ext
      · rfl
      · apply heq_of_eq
        simpa only [generatedToManySortedAt_dataSort] using
          generatedToManySorted_generatedFromManySorted D dataSort left
      · apply heq_of_eq
        simpa only [generatedToManySortedAt_dataSort] using
          generatedToManySorted_generatedFromManySorted D dataSort right

noncomputable def truthToManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma} :
    GammaTruth D -> ManySorted.GammaTruth (toManySortedPartialAlg D)
  | .trueValue => .trueValue
  | .failure failure => .failure (failureToManySorted failure)

noncomputable def truthFromManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma} :
    ManySorted.GammaTruth (toManySortedPartialAlg D) -> GammaTruth D
  | .trueValue => .trueValue
  | .failure failure => .failure (failureFromManySorted failure)

@[simp] theorem truthFromManySorted_truthToManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (truth : GammaTruth D) :
    truthFromManySorted (truthToManySorted truth) = truth := by
  cases truth <;> simp [truthToManySorted, truthFromManySorted]

@[simp] theorem truthToManySorted_truthFromManySorted
    {Sigma : Resolution.Signature.{u}}
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (truth : ManySorted.GammaTruth (toManySortedPartialAlg D)) :
    truthToManySorted (truthFromManySorted truth) = truth := by
  cases truth <;> simp [truthToManySorted, truthFromManySorted]

/-- Existence equality commutes with the carrier and truth translations. -/
theorem truthToManySorted_gammaExistenceEq
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (left right : Free.GeneratedAns D) :
    truthToManySorted (gammaExistenceEq D left right) =
      ManySorted.gammaExistenceEq (toManySortedPartialAlg D) dataSort
        (generatedToManySorted D left) (generatedToManySorted D right) := by
  by_cases hSame : SameOld D left right
  · have hMany := (sameOld_iff D left right).1 hSame
    simp [gammaExistenceEq, ManySorted.gammaExistenceEq, hSame, hMany,
      truthToManySorted]
  · have hMany : Not (ManySorted.SameOld (toManySortedPartialAlg D)
        (generatedToManySorted D left) (generatedToManySorted D right)) :=
      fun h => hSame ((sameOld_iff D left right).2 h)
    simp [gammaExistenceEq, ManySorted.gammaExistenceEq, hSame, hMany,
      truthToManySorted, failureToManySorted]

/-- Equivalence of binary encoded algebras, including both carriers and all
encoded operations. -/
structure EncodedAlgEquiv
    {Sigma : Resolution.Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (N : EncodedAlg.{u,x,y} Sigma) where
  dataEquiv : CarrierEquiv M.Data N.Data
  truthEquiv : CarrierEquiv M.Truth N.Truth
  map_op : forall (operation : Sigma.Op) (left right : M.Data),
    dataEquiv.toFun (M.op operation left right) =
      N.op operation (dataEquiv.toFun left) (dataEquiv.toFun right)
  map_existenceEq : forall left right : M.Data,
    truthEquiv.toFun (M.existenceEq left right) =
      N.existenceEq (dataEquiv.toFun left) (dataEquiv.toFun right)
  map_true : truthEquiv.toFun M.trueValue = N.trueValue

namespace EncodedAlgEquiv

/-- The inverse data equivalence also preserves every encoded operation. -/
theorem inv_map_op
    {Sigma : Resolution.Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (equiv : EncodedAlgEquiv M N)
    (operation : Sigma.Op)
    (left right : N.Data) :
    equiv.dataEquiv.invFun (N.op operation left right) =
      M.op operation (equiv.dataEquiv.invFun left)
        (equiv.dataEquiv.invFun right) := by
  calc
    equiv.dataEquiv.invFun (N.op operation left right) =
        equiv.dataEquiv.invFun
          (N.op operation
            (equiv.dataEquiv.toFun (equiv.dataEquiv.invFun left))
            (equiv.dataEquiv.toFun (equiv.dataEquiv.invFun right))) := by
      rw [equiv.dataEquiv.right_inv, equiv.dataEquiv.right_inv]
    _ = equiv.dataEquiv.invFun
          (equiv.dataEquiv.toFun
            (M.op operation (equiv.dataEquiv.invFun left)
              (equiv.dataEquiv.invFun right))) :=
      congrArg equiv.dataEquiv.invFun
        (equiv.map_op operation (equiv.dataEquiv.invFun left)
          (equiv.dataEquiv.invFun right)).symm
    _ = M.op operation (equiv.dataEquiv.invFun left)
          (equiv.dataEquiv.invFun right) :=
      equiv.dataEquiv.left_inv _

/-- The inverse truth equivalence preserves existence equality. -/
theorem inv_map_existenceEq
    {Sigma : Resolution.Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (equiv : EncodedAlgEquiv M N)
    (left right : N.Data) :
    equiv.truthEquiv.invFun (N.existenceEq left right) =
      M.existenceEq (equiv.dataEquiv.invFun left)
        (equiv.dataEquiv.invFun right) := by
  calc
    equiv.truthEquiv.invFun (N.existenceEq left right) =
        equiv.truthEquiv.invFun
          (N.existenceEq
            (equiv.dataEquiv.toFun (equiv.dataEquiv.invFun left))
            (equiv.dataEquiv.toFun (equiv.dataEquiv.invFun right))) := by
      rw [equiv.dataEquiv.right_inv, equiv.dataEquiv.right_inv]
    _ = equiv.truthEquiv.invFun
          (equiv.truthEquiv.toFun
            (M.existenceEq (equiv.dataEquiv.invFun left)
              (equiv.dataEquiv.invFun right))) :=
      congrArg equiv.truthEquiv.invFun
        (equiv.map_existenceEq (equiv.dataEquiv.invFun left)
          (equiv.dataEquiv.invFun right)).symm
    _ = M.existenceEq (equiv.dataEquiv.invFun left)
          (equiv.dataEquiv.invFun right) :=
      equiv.truthEquiv.left_inv _

/-- The inverse truth equivalence preserves the distinguished truth value. -/
theorem inv_map_true
    {Sigma : Resolution.Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (equiv : EncodedAlgEquiv M N) :
    equiv.truthEquiv.invFun N.trueValue = M.trueValue := by
  calc
    equiv.truthEquiv.invFun N.trueValue =
        equiv.truthEquiv.invFun
          (equiv.truthEquiv.toFun M.trueValue) :=
      congrArg equiv.truthEquiv.invFun equiv.map_true.symm
    _ = M.trueValue := equiv.truthEquiv.left_inv _

end EncodedAlgEquiv

/-- The auxiliary truth carriers in the two canonical encodings are
canonically equivalent. -/
noncomputable def gammaTruthEquiv
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    CarrierEquiv (GammaTruth D)
      (ManySorted.GammaTruth (toManySortedPartialAlg D)) where
  toFun := truthToManySorted
  invFun := truthFromManySorted
  left_inv := truthFromManySorted_truthToManySorted
  right_inv := truthToManySorted_truthFromManySorted

/-- Main specialization theorem: the existing binary canonical encoding is
formally equivalent to the binary one-sorted instance of the autonomous
many-sorted canonical encoding.  The equivalence respects generated
operations, existence equality, and the distinguished truth value. -/
noncomputable def gammaEquiv
    {Sigma : Resolution.Signature.{u}}
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    EncodedAlgEquiv (gamma D)
      (fromManySortedEncodedAlg
        (ManySorted.gamma (toManySortedPartialAlg D))) where
  dataEquiv := generatedEquiv D
  truthEquiv := gammaTruthEquiv D
  map_op := generatedToManySorted_op D
  map_existenceEq := truthToManySorted_gammaExistenceEq D
  map_true := rfl

end BinarySpecialization
end Diaconescu
end Resolution
