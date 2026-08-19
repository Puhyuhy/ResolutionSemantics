import ResolutionStrongTotality

/-!
# Functoriality of Strong Totality

Strong Totality should be stable under mathematically valid translations of
specifications.  This module equips typed specifications with morphisms that
send accepted candidates to accepted candidates and proves that Resolution
Answers transport functorially along such morphisms.

The residual is preserved exactly.  Thus a change of mathematical language or
representation cannot silently turn an unresolved answer into an ordinary
solution, while every genuine solution is transported conservatively.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- A morphism of mathematical specifications sends candidate answers forward
and preserves validity. -/
structure SpecMorphism (S T : Specification.{u}) where
  map : S.Candidate -> T.Candidate
  preserves : forall x : S.Candidate, S.accepts x -> T.accepts (map x)

namespace SpecMorphism

/-- Identity translation of a specification. -/
def id (S : Specification.{u}) : SpecMorphism S S where
  map := fun x => x
  preserves := fun _ hx => hx

/-- Composition of validity-preserving translations. -/
def comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T) : SpecMorphism S U where
  map := fun x => g.map (f.map x)
  preserves := fun x hx => g.preserves (f.map x) (f.preserves x hx)

/-- A specification morphism acts on ordinary satisfying solutions. -/
def mapSolution
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    Specification.Solution S -> Specification.Solution T
  | ⟨x, hx⟩ => ⟨f.map x, f.preserves x hx⟩

@[simp] theorem mapSolution_id
    (S : Specification.{u})
    (x : Specification.Solution S) :
    mapSolution (id S) x = x := by
  cases x
  rfl

@[simp] theorem mapSolution_comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T)
    (x : Specification.Solution S) :
    mapSolution (comp g f) x = mapSolution g (mapSolution f x) := by
  cases x
  rfl

end SpecMorphism

namespace ResolutionAnswer

/-- Transport a Resolution Answer along a validity-preserving translation of
specifications.  Realized answers map to realized answers; residuals remain
residuals. -/
def map
    {S T : Specification.{u}}
    (f : SpecMorphism S T) : ResolutionAnswer S -> ResolutionAnswer T
  | .realized x hx => .realized (f.map x) (f.preserves x hx)
  | .residual => .residual

@[simp] theorem map_realized
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (x : S.Candidate)
    (hx : S.accepts x) :
    map f (.realized x hx) = .realized (f.map x) (f.preserves x hx) := by
  rfl

@[simp] theorem map_residual
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    map f (ResolutionAnswer.residual : ResolutionAnswer S) = .residual := by
  rfl

/-- Conservativity is natural: translating an embedded ordinary solution is
the same as first translating the solution and then embedding it. -/
@[simp] theorem map_realizeSolution
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (x : Specification.Solution S) :
    map f (realizeSolution x) =
      realizeSolution (SpecMorphism.mapSolution f x) := by
  cases x
  rfl

/-- Resolution transport respects identity translations. -/
@[simp] theorem map_id
    (S : Specification.{u})
    (a : ResolutionAnswer S) :
    map (SpecMorphism.id S) a = a := by
  cases a <;> rfl

/-- Resolution transport respects composition of specification translations. -/
@[simp] theorem map_comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T)
    (a : ResolutionAnswer S) :
    map (SpecMorphism.comp g f) a = map g (map f a) := by
  cases a <;> rfl

/-- Forgetting to an optional ordinary solution is natural with respect to
specification morphisms. -/
theorem solution?_map
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (a : ResolutionAnswer S) :
    (map f a).solution? = Option.map (SpecMorphism.mapSolution f) a.solution? := by
  cases a <;> rfl

/-- Canonical totalization commutes with translation of specifications.  This is
the naturality square connecting partial ordinary solution data with total
Resolution data. -/
theorem map_totalize
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (a : Option (Specification.Solution S)) :
    map f (totalize S a) =
      totalize T (Option.map (SpecMorphism.mapSolution f) a) := by
  cases a <;> rfl

end ResolutionAnswer

/-- Strong Totality is invariant under specification translation in the precise
sense that every existing Resolution Answer transports to one for the target
specification. -/
def strongTotality_natural
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    ResolutionAnswer S -> ResolutionAnswer T :=
  ResolutionAnswer.map f

/-- A realized solution can never become residual merely by translating the
specification. -/
theorem realized_translation_ne_residual
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (x : Specification.Solution S) :
    ResolutionAnswer.map f (realizeSolution x) ≠
      (ResolutionAnswer.residual : ResolutionAnswer T) := by
  rw [ResolutionAnswer.map_realizeSolution]
  exact realizeSolution_ne_residual (SpecMorphism.mapSolution f x)

/-! ## Naturality for families of specifications -/

/-- Translate a partial resolver pointwise along a family of specification
morphisms. -/
def mapPartialResolver
    {I : Type v}
    {F G : I -> Specification.{u}}
    (eta : forall i : I, SpecMorphism (F i) (G i))
    (r : PartialResolver F) : PartialResolver G :=
  fun i => Option.map (SpecMorphism.mapSolution (eta i)) (r i)

/-- Translate a total Resolution resolver pointwise. -/
def mapResolver
    {I : Type v}
    {F G : I -> Specification.{u}}
    (eta : forall i : I, SpecMorphism (F i) (G i))
    (R : Resolver F) : Resolver G :=
  fun i => ResolutionAnswer.map (eta i) (R i)

/-- Pointwise Strong Totality is natural: translating after totalization is
identical to translating the partial resolver first and then totalizing. -/
theorem totalizeResolver_natural
    {I : Type v}
    {F G : I -> Specification.{u}}
    (eta : forall i : I, SpecMorphism (F i) (G i))
    (r : PartialResolver F) :
    mapResolver eta (totalizeResolver F r) =
      totalizeResolver G (mapPartialResolver eta r) := by
  funext i
  exact ResolutionAnswer.map_totalize (eta i) (r i)

end StrongTotality
end Resolution
