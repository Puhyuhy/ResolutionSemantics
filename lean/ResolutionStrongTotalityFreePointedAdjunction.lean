import ResolutionStrongTotalityNormalForm
import ResolutionStrongTotalityFunctorial

/-!
# Free pointed completion and the global shape of Strong Totality

The minimal Resolution construction has the standard categorical shape of a
free pointed object.  For a type `X`, freely adjoining one distinguished point
produces `X ⊕ Unit`.  Maps from this free pointed type into any pointed target
are in canonical bijection with ordinary functions from `X` into the target
carrier.

This is precisely the hom-set form of the left adjunction between adjoining a
basepoint and forgetting the basepoint.  We formalize only that small amount of
category theory directly, without importing an external category library.

The Strong Totality construction then fits this standard pattern exactly:
`ResolutionAnswer S` is the free pointed completion of the ordinary solution
type of `S`, and transport along a specification morphism is the unique pointed
extension of transport on ordinary solutions.
-/

universe u v w

namespace Resolution
namespace StrongTotality

/-- A type equipped with one distinguished point. -/
structure PointedType where
  Carrier : Type u
  point : Carrier

/-- A map of pointed types preserves the distinguished point. -/
structure PointedHom (A : PointedType.{u}) (B : PointedType.{v}) where
  toFun : A.Carrier -> B.Carrier
  map_point : toFun A.point = B.point

namespace PointedHom

/-- Identity pointed map. -/
def id (A : PointedType.{u}) : PointedHom A A where
  toFun := fun x => x
  map_point := rfl

/-- Composition of pointed maps. -/
def comp
    {A : PointedType.{u}}
    {B : PointedType.{v}}
    {C : PointedType.{w}}
    (g : PointedHom B C)
    (f : PointedHom A B) : PointedHom A C where
  toFun := fun x => g.toFun (f.toFun x)
  map_point := by
    calc
      g.toFun (f.toFun A.point) = g.toFun B.point :=
        congrArg g.toFun f.map_point
      _ = C.point := g.map_point

/-- Extensionality for pointed maps. -/
theorem ext
    {A : PointedType.{u}}
    {B : PointedType.{v}}
    (f g : PointedHom A B)
    (h : forall x : A.Carrier, f.toFun x = g.toFun x) :
    f = g := by
  cases f with
  | mk fto fp =>
      cases g with
      | mk gto gp =>
          have hfun : fto = gto := by
            funext x
            exact h x
          cases hfun
          rfl

end PointedHom

/-- Freely adjoin one distinguished point to a type. -/
def freePointed (X : Type u) : PointedType.{u} where
  Carrier := Sum X Unit
  point := Sum.inr ()

/-- Functorial action of the free-pointed construction. -/
def freePointedMap
    {X : Type u}
    {Y : Type v}
    (f : X -> Y) : PointedHom (freePointed X) (freePointed Y) where
  toFun := fun a =>
    match a with
    | .inl x => .inl (f x)
    | .inr _ => .inr ()
  map_point := rfl

/-- Free-pointed transport preserves identity. -/
theorem freePointedMap_id
    (X : Type u) :
    freePointedMap (fun x : X => x) = PointedHom.id (freePointed X) := by
  apply PointedHom.ext
  intro a
  cases a with
  | inl x => rfl
  | inr q =>
      cases q
      rfl

/-- Free-pointed transport preserves composition. -/
theorem freePointedMap_comp
    {X : Type u}
    {Y : Type v}
    {Z : Type w}
    (g : Y -> Z)
    (f : X -> Y) :
    freePointedMap (fun x => g (f x)) =
      PointedHom.comp (freePointedMap g) (freePointedMap f) := by
  apply PointedHom.ext
  intro a
  cases a with
  | inl x => rfl
  | inr q =>
      cases q
      rfl

/-- Extend an arbitrary function from `X` uniquely over the freely adjoined
point by sending the new point to the distinguished point of the target. -/
def freePointedExtend
    (X : Type u)
    (P : PointedType.{v})
    (f : X -> P.Carrier) : PointedHom (freePointed X) P where
  toFun := fun a =>
    match a with
    | .inl x => f x
    | .inr _ => P.point
  map_point := rfl

/-- Restrict a pointed map from the free pointed type to the original type. -/
def freePointedRestrict
    (X : Type u)
    (P : PointedType.{v})
    (g : PointedHom (freePointed X) P) : X -> P.Carrier :=
  fun x => g.toFun (Sum.inl x)

/-- Hom-set form of the free-pointed adjunction:

`PointedHom (X + 1) P ≃ (X -> P)`.

This is the categorical reason that adjoining one residual point is the free
pointed completion rather than an arbitrary totalization. -/
def freePointedAdjunctionHomEquiv
    (X : Type u)
    (P : PointedType.{v}) :
    Equiv (PointedHom (freePointed X) P) (X -> P.Carrier) where
  toFun := freePointedRestrict X P
  invFun := freePointedExtend X P
  left_inv := by
    intro g
    apply PointedHom.ext
    intro a
    cases a with
    | inl x => rfl
    | inr q =>
        cases q
        change P.point = g.toFun (freePointed X).point
        exact g.map_point.symm
  right_inv := by
    intro f
    funext x
    rfl

/-- Naturality of the free-pointed hom equivalence in the source type. -/
theorem freePointedAdjunction_source_natural
    {X : Type u}
    {Y : Type v}
    (f : X -> Y)
    (P : PointedType.{w})
    (g : PointedHom (freePointed Y) P)
    (x : X) :
    freePointedAdjunctionHomEquiv X P
        (PointedHom.comp g (freePointedMap f)) x =
      freePointedAdjunctionHomEquiv Y P g (f x) := by
  rfl

/-- Naturality of the free-pointed hom equivalence in the pointed target. -/
theorem freePointedAdjunction_target_natural
    (X : Type u)
    {P : PointedType.{v}}
    {Q : PointedType.{w}}
    (h : PointedHom P Q)
    (g : PointedHom (freePointed X) P)
    (x : X) :
    freePointedAdjunctionHomEquiv X Q (PointedHom.comp h g) x =
      h.toFun (freePointedAdjunctionHomEquiv X P g x) := by
  rfl

/-- The Resolution answer space, viewed only as a pointed type. -/
def resolutionPointed
    (S : Specification.{u}) : PointedType.{u} where
  Carrier := ResolutionAnswer S
  point := ResolutionAnswer.residual

/-- A specification morphism induces a pointed map of Resolution spaces. -/
def resolutionPointedMap
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    PointedHom (resolutionPointed S) (resolutionPointed T) where
  toFun := ResolutionAnswer.map f
  map_point := ResolutionAnswer.map_residual f

/-- The pointed Resolution action preserves identity. -/
theorem resolutionPointedMap_id
    (S : Specification.{u}) :
    resolutionPointedMap (SpecMorphism.id S) =
      PointedHom.id (resolutionPointed S) := by
  apply PointedHom.ext
  intro a
  exact ResolutionAnswer.map_id S a

/-- The pointed Resolution action preserves composition. -/
theorem resolutionPointedMap_comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T) :
    resolutionPointedMap (SpecMorphism.comp g f) =
      PointedHom.comp (resolutionPointedMap g) (resolutionPointedMap f) := by
  apply PointedHom.ext
  intro a
  exact ResolutionAnswer.map_comp g f a

/-- The canonical normal form identifies Resolution with the free pointed type
on the ordinary solution space. -/
def resolutionPointedEquivFree
    (S : Specification.{u}) :
    Equiv (resolutionPointed S).Carrier
      (freePointed (Specification.Solution S)).Carrier :=
  resolutionAnswerEquivSum S

/-- The normal-form equivalence sends the Resolution residual exactly to the
freely adjoined point. -/
theorem resolutionPointedEquivFree_point
    (S : Specification.{u}) :
    resolutionPointedEquivFree S (resolutionPointed S).point =
      (freePointed (Specification.Solution S)).point :=
  resolutionAnswerEquivSum_residual S

/-- Extend a function on ordinary solutions uniquely to a pointed map out of
Resolution Answers. -/
def resolutionPointedExtend
    (S : Specification.{u})
    (P : PointedType.{v})
    (f : Specification.Solution S -> P.Carrier) :
    PointedHom (resolutionPointed S) P where
  toFun := ResolutionAnswer.fold f P.point
  map_point := rfl

/-- Restrict a pointed map out of Resolution Answers to ordinary solutions. -/
def resolutionPointedRestrict
    (S : Specification.{u})
    (P : PointedType.{v})
    (g : PointedHom (resolutionPointed S) P) :
    Specification.Solution S -> P.Carrier :=
  fun x => g.toFun (realizeSolution x)

/-- Resolution itself satisfies the free-pointed hom-set equivalence directly. -/
def resolutionPointedHomEquiv
    (S : Specification.{u})
    (P : PointedType.{v}) :
    Equiv (PointedHom (resolutionPointed S) P)
      (Specification.Solution S -> P.Carrier) where
  toFun := resolutionPointedRestrict S P
  invFun := resolutionPointedExtend S P
  left_inv := by
    intro g
    apply PointedHom.ext
    intro a
    cases a with
    | realized x hx => rfl
    | residual =>
        change P.point = g.toFun (resolutionPointed S).point
        exact g.map_point.symm
  right_inv := by
    intro f
    funext x
    cases x
    rfl

/-- Canonical Resolution transport is not additional structure: it is exactly
the free pointed extension of transport on ordinary solutions. -/
theorem resolutionPointedMap_isFreeExtension
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    resolutionPointedMap f =
      resolutionPointedExtend S (resolutionPointed T)
        (fun x => realizeSolution (SpecMorphism.mapSolution f x)) := by
  apply PointedHom.ext
  intro a
  cases a with
  | realized x hx => rfl
  | residual => rfl

/-- Compact characterization: the Resolution carrier is `Solution + 1`, and
maps from it to every pointed target are exactly ordinary functions defined on
solutions.  This is the free-pointed/left-adjoint form of Strong Totality. -/
structure ResolutionFreePointedCharacterization
    (S : Specification.{u}) : Prop where
  carrierFree :
    Nonempty
      (Equiv (resolutionPointed S).Carrier
        (freePointed (Specification.Solution S)).Carrier)
  universalHom :
    forall P : PointedType.{u},
      Nonempty
        (Equiv (PointedHom (resolutionPointed S) P)
          (Specification.Solution S -> P.Carrier))
  transportIsFreeExtension :
    forall {T : Specification.{u}} (f : SpecMorphism S T),
      resolutionPointedMap f =
        resolutionPointedExtend S (resolutionPointed T)
          (fun x => realizeSolution (SpecMorphism.mapSolution f x))

/-- Resolution satisfies the free-pointed characterization canonically. -/
theorem resolution_freePointedCharacterization
    (S : Specification.{u}) :
    ResolutionFreePointedCharacterization S := by
  exact {
    carrierFree := ⟨resolutionPointedEquivFree S⟩
    universalHom := fun P => ⟨resolutionPointedHomEquiv S P⟩
    transportIsFreeExtension := fun f =>
      resolutionPointedMap_isFreeExtension f
  }

end StrongTotality
end Resolution
