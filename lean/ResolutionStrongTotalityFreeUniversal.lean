import ResolutionStrongTotalityFreeBridge

/-!
# Free-algebra universality on the Strong Totality presentation

The preceding bridge identifies `Free.GeneratedAns D` with a structured Strong
Totality answer type.  This module transports the existing free-algebra
structure and universal property across that equivalence.

Consequently the same object admits two complementary characterizations:

* algebraically, it is the generated free completion of the partial algebra;
* semantically, it is a provenance-preserving Strong Totality answer space.

No new quotient or competing completion is introduced.  The operations and the
universal map below are transported from the already-proved `Free` layer.
-/

universe u v w

namespace Resolution
namespace StrongTotality

variable {Sigma : Signature.{u}}

/-- Old generators in the Strong Totality presentation of the free algebra. -/
def generatedStrongOld
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) : GeneratedStrongAnswer D :=
  generatedAnsToStrong D (Free.generatedOld D a)

/-- The free algebra operation transported to the Strong Totality
presentation. -/
def generatedStrongOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : GeneratedStrongAnswer D) : GeneratedStrongAnswer D :=
  generatedAnsToStrong D
    (Free.generatedOp D f
      (strongToGeneratedAns D x)
      (strongToGeneratedAns D y))

@[simp] theorem strongToGeneratedAns_generatedStrongOld
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) :
    strongToGeneratedAns D (generatedStrongOld D a) =
      Free.generatedOld D a := by
  exact strongToGeneratedAns_generatedAnsToStrong D (Free.generatedOld D a)

@[simp] theorem strongToGeneratedAns_generatedStrongOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : GeneratedStrongAnswer D) :
    strongToGeneratedAns D (generatedStrongOp D f x y) =
      Free.generatedOp D f
        (strongToGeneratedAns D x)
        (strongToGeneratedAns D y) := by
  exact strongToGeneratedAns_generatedAnsToStrong D
    (Free.generatedOp D f
      (strongToGeneratedAns D x)
      (strongToGeneratedAns D y))

@[simp] theorem generatedAnsToStrong_generatedOld
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) :
    generatedAnsToStrong D (Free.generatedOld D a) =
      generatedStrongOld D a := by
  rfl

@[simp] theorem generatedAnsToStrong_generatedOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    generatedAnsToStrong D (Free.generatedOp D f x y) =
      generatedStrongOp D f
        (generatedAnsToStrong D x)
        (generatedAnsToStrong D y) := by
  unfold generatedStrongOp
  rw [strongToGeneratedAns_generatedAnsToStrong,
      strongToGeneratedAns_generatedAnsToStrong]

/-- A homomorphism from the Strong Totality presentation of the generated free
algebra into an already-compatible total algebra. -/
structure StrongCompatibleHom
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D) where
  toFun : GeneratedStrongAnswer D -> T.Carrier
  map_old : forall a : D.Carrier,
    toFun (generatedStrongOld D a) = T.embed a
  map_op : forall (f : Sigma.Op) (x y : GeneratedStrongAnswer D),
    toFun (generatedStrongOp D f x y) =
      T.op f (toFun x) (toFun y)

namespace StrongCompatibleHom

/-- Extensionality for transported compatible homomorphisms. -/
theorem ext
    {D : PartialAlg.{u,v} Sigma}
    {T : Free.CompatibleAlg.{u,v,w} D}
    {F G : StrongCompatibleHom D T}
    (h : F.toFun = G.toFun) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Convert a homomorphism on the Strong Totality presentation back to the
existing free-algebra presentation. -/
def toFree
    {D : PartialAlg.{u,v} Sigma}
    {T : Free.CompatibleAlg.{u,v,w} D}
    (F : StrongCompatibleHom D T) : Free.CompatibleHom D T where
  toFun := fun x => F.toFun (generatedAnsToStrong D x)
  map_old := by
    intro a
    exact F.map_old a
  map_op := by
    intro f x y
    have h := F.map_op f
      (generatedAnsToStrong D x)
      (generatedAnsToStrong D y)
    simpa using h

/-- Transport an existing free compatible homomorphism to the Strong Totality
presentation. -/
def ofFree
    {D : PartialAlg.{u,v} Sigma}
    {T : Free.CompatibleAlg.{u,v,w} D}
    (F : Free.CompatibleHom D T) : StrongCompatibleHom D T where
  toFun := fun a => F.toFun (strongToGeneratedAns D a)
  map_old := by
    intro a
    simpa using F.map_old a
  map_op := by
    intro f x y
    simpa using F.map_op f
      (strongToGeneratedAns D x)
      (strongToGeneratedAns D y)

@[simp] theorem ofFree_toFree
    {D : PartialAlg.{u,v} Sigma}
    {T : Free.CompatibleAlg.{u,v,w} D}
    (F : StrongCompatibleHom D T) :
    ofFree (toFree F) = F := by
  apply ext
  funext a
  exact congrArg F.toFun
    (generatedAnsToStrong_strongToGeneratedAns D a)

@[simp] theorem toFree_ofFree
    {D : PartialAlg.{u,v} Sigma}
    {T : Free.CompatibleAlg.{u,v,w} D}
    (F : Free.CompatibleHom D T) :
    toFree (ofFree F) = F := by
  apply Free.CompatibleHom.ext
  funext x
  exact congrArg F.toFun
    (strongToGeneratedAns_generatedAnsToStrong D x)

/-- Compatible homomorphisms from the two equivalent presentations are
themselves equivalent. -/
def equivFree
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D) :
    Equiv (StrongCompatibleHom D T) (Free.CompatibleHom D T) where
  toFun := toFree
  invFun := ofFree
  left_inv := ofFree_toFree
  right_inv := toFree_ofFree

end StrongCompatibleHom

/-- The canonical interpretation of the Strong Totality/free-algebra
presentation into any compatible total algebra. -/
noncomputable def strongCompatibleInterpHom
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D) : StrongCompatibleHom D T :=
  StrongCompatibleHom.ofFree (Free.compatibleInterpHom D T)

/-- The transported canonical interpretation agrees pointwise with the existing
free interpretation after decoding the Strong Totality presentation. -/
@[simp] theorem strongCompatibleInterpHom_apply
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D)
    (a : GeneratedStrongAnswer D) :
    (strongCompatibleInterpHom D T).toFun a =
      Free.CompatibleAlg.interp D T (strongToGeneratedAns D a) := by
  rfl

/-- Uniqueness transports across the presentation equivalence: every compatible
homomorphism out of `GeneratedStrongAnswer D` is the canonical one. -/
theorem strongCompatibleHom_unique
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D)
    (F : StrongCompatibleHom D T) :
    F = strongCompatibleInterpHom D T := by
  have hfree : StrongCompatibleHom.toFree F =
      Free.compatibleInterpHom D T :=
    Free.compatibleHom_unique D T (StrongCompatibleHom.toFree F)
  calc
    F = StrongCompatibleHom.ofFree (StrongCompatibleHom.toFree F) :=
      (StrongCompatibleHom.ofFree_toFree F).symm
    _ = StrongCompatibleHom.ofFree (Free.compatibleInterpHom D T) :=
      congrArg StrongCompatibleHom.ofFree hfree
    _ = strongCompatibleInterpHom D T := rfl

/-- Universal property in the Strong Totality presentation: into every
compatible total algebra there exists exactly one structure-preserving map. -/
theorem generatedStrong_has_unique_compatibleHom
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D) :
    Exists fun F : StrongCompatibleHom D T =>
      forall G : StrongCompatibleHom D T, G = F := by
  refine ⟨strongCompatibleInterpHom D T, ?_⟩
  intro G
  exact strongCompatibleHom_unique D T G

/-- The free-algebra universal property and the provenance-preserving Strong
Totality presentation are therefore two presentations of one universal object. -/
theorem generatedStrong_isFreePresentation
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.CompatibleAlg.{u,v,w} D) :
    Nonempty (StrongCompatibleHom D T) := by
  exact ⟨strongCompatibleInterpHom D T⟩

end StrongTotality
end Resolution
