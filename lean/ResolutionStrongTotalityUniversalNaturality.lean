import ResolutionStrongTotalityCompletionCategory

/-!
# Universal naturality of the Strong Totality completion

The canonical completion is universal not only inside the category of
completions of one fixed specification.  A validity-preserving translation
`f : S -> T` also determines how ordinary certified solutions of `S` are to be
seen inside any pointed completion of `T`.

A completion map *over `f`* therefore sends each embedded solution `x` of `S`
to the embedding of `f(x)` in the target completion and preserves the residual.
The canonical Resolution completion of `S` admits exactly one such map into
any completion of `T`.

Specializing the target to the canonical completion of `T`, the unique map is
exactly `ResolutionAnswer.map f`.  Hence the functorial action of Resolution
Answers is forced by the universal property rather than being an independent
choice.  Identity and composition follow both computationally and by
uniqueness.

More generally, any universal completion may replace the canonical source.
It has a unique map over every specification morphism into every pointed target.
When both source and target are universal, their unique canonical
isomorphisms make this map commute with the canonical Resolution action.  Thus
canonicity and naturality are coherent consequences of one universal property.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- A map from a completion over `S` to a completion over `T`, lying over a
specification morphism `f : S -> T`. -/
structure CompletionHomOver
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (A : CompletionObject S)
    (B : CompletionObject T) where
  toFun : A.Carrier -> B.Carrier
  map_solution : forall x : Specification.Solution S,
    toFun (A.includeSolution x) =
      B.includeSolution (SpecMorphism.mapSolution f x)
  map_residual : toFun A.residual = B.residual

namespace CompletionHomOver

/-- A vertical completion morphism is the same data as a map over the identity
specification morphism. -/
def ofVertical
    {S : Specification.{u}}
    {A B : CompletionObject S}
    (g : CompletionHom A B) :
    CompletionHomOver (SpecMorphism.id S) A B where
  toFun := g.toFun
  map_solution := by
    intro x
    simpa using g.map_solution x
  map_residual := g.map_residual

/-- Identity map over the identity specification translation. -/
def id
    {S : Specification.{u}}
    (A : CompletionObject S) :
    CompletionHomOver (SpecMorphism.id S) A A :=
  ofVertical (CompletionHom.id A)

/-- Compose completion maps lying over composable specification maps. -/
def comp
    {S T U : Specification.{u}}
    {A : CompletionObject S}
    {B : CompletionObject T}
    {C : CompletionObject U}
    {f : SpecMorphism S T}
    {g : SpecMorphism T U}
    (q : CompletionHomOver g B C)
    (p : CompletionHomOver f A B) :
    CompletionHomOver (SpecMorphism.comp g f) A C where
  toFun := fun x => q.toFun (p.toFun x)
  map_solution := by
    intro x
    rw [p.map_solution x, q.map_solution (SpecMorphism.mapSolution f x)]
    rfl
  map_residual := by
    rw [p.map_residual, q.map_residual]

/-- Precompose a map over `f` by a vertical morphism in the source fiber. -/
def precompVertical
    {S T : Specification.{u}}
    {f : SpecMorphism S T}
    {A A' : CompletionObject S}
    {B : CompletionObject T}
    (p : CompletionHomOver f A B)
    (g : CompletionHom A' A) :
    CompletionHomOver f A' B where
  toFun := fun x => p.toFun (g.toFun x)
  map_solution := by
    intro x
    rw [g.map_solution x, p.map_solution x]
  map_residual := by
    rw [g.map_residual, p.map_residual]

/-- Postcompose a map over `f` by a vertical morphism in the target fiber. -/
def postcompVertical
    {S T : Specification.{u}}
    {f : SpecMorphism S T}
    {A : CompletionObject S}
    {B B' : CompletionObject T}
    (g : CompletionHom B B')
    (p : CompletionHomOver f A B) :
    CompletionHomOver f A B' where
  toFun := fun x => g.toFun (p.toFun x)
  map_solution := by
    intro x
    rw [p.map_solution x,
      g.map_solution (SpecMorphism.mapSolution f x)]
  map_residual := by
    rw [p.map_residual, g.map_residual]

/-- Extensionality of completion maps over a fixed specification translation. -/
theorem ext
    {S T : Specification.{u}}
    {f : SpecMorphism S T}
    {A : CompletionObject S}
    {B : CompletionObject T}
    (p q : CompletionHomOver f A B)
    (h : forall x : A.Carrier, p.toFun x = q.toFun x) :
    p = q := by
  cases p with
  | mk pto psol pres =>
      cases q with
      | mk qto qsol qres =>
          have hfun : pto = qto := by
            funext x
            exact h x
          cases hfun
          rfl

end CompletionHomOver

/-- The universal map from the canonical completion of `S` into an arbitrary
completion of `T`, over a specification translation `f : S -> T`. -/
def canonicalCompletionMapOver
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (B : CompletionObject T) :
    CompletionHomOver f (canonicalCompletion S) B where
  toFun := ResolutionAnswer.fold
    (fun x => B.includeSolution (SpecMorphism.mapSolution f x))
    B.residual
  map_solution := by
    intro x
    cases x
    rfl
  map_residual := rfl

/-- Relative initiality: after fixing the base translation `f : S -> T`, there
is exactly one structure-preserving map from the canonical Resolution
completion of `S` into any pointed completion of `T`. -/
theorem canonicalCompletion_relativeInitial
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (B : CompletionObject T) :
    Exists fun p : CompletionHomOver f (canonicalCompletion S) B =>
      forall q : CompletionHomOver f (canonicalCompletion S) B, q = p := by
  refine ⟨canonicalCompletionMapOver f B, ?_⟩
  intro q
  apply CompletionHomOver.ext
  intro a
  cases a with
  | realized x hx =>
      have h := q.map_solution (⟨x, hx⟩ : Specification.Solution S)
      simpa [canonicalCompletion, canonicalCompletionMapOver, realizeSolution]
        using h
  | residual =>
      simpa [canonicalCompletion, canonicalCompletionMapOver]
        using q.map_residual

/-- Direct uniqueness form of relative initiality. -/
theorem canonicalCompletionMapOver_unique
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (B : CompletionObject T)
    (q : CompletionHomOver f (canonicalCompletion S) B) :
    q = canonicalCompletionMapOver f B := by
  rcases canonicalCompletion_relativeInitial f B with ⟨p, huniq⟩
  have hq : q = p := huniq q
  have hc : canonicalCompletionMapOver f B = p :=
    huniq (canonicalCompletionMapOver f B)
  exact hq.trans hc.symm

/-- Relative initiality does not depend on choosing the canonical presentation
of the source.  Every universal pointed completion has exactly one map over
`f` into every pointed target completion. -/
theorem universalCompletion_relativeInitial
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (A : CompletionObject S)
    (B : CompletionObject T)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual) :
    Exists fun p : CompletionHomOver f A B =>
      forall q : CompletionHomOver f A B, q = p := by
  rcases hA B.Carrier
      (fun x : Specification.Solution S =>
        B.includeSolution (SpecMorphism.mapSolution f x))
      B.residual with
    ⟨F, hF, hUnique⟩
  let p : CompletionHomOver f A B := {
    toFun := F
    map_solution := hF.1
    map_residual := hF.2
  }
  refine ⟨p, ?_⟩
  intro q
  have hqPreserves :
      ((forall x : Specification.Solution S,
          q.toFun (A.includeSolution x) =
            B.includeSolution (SpecMorphism.mapSolution f x)) ∧
        q.toFun A.residual = B.residual) :=
    ⟨q.map_solution, q.map_residual⟩
  have hqFun : q.toFun = F := hUnique q.toFun hqPreserves
  apply CompletionHomOver.ext
  intro x
  change q.toFun x = F x
  exact congrFun hqFun x

/-- The already-defined functorial map on Resolution Answers, packaged as a
completion map over the corresponding specification morphism. -/
def canonicalCompletionFunctorMap
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    CompletionHomOver f (canonicalCompletion S) (canonicalCompletion T) where
  toFun := ResolutionAnswer.map f
  map_solution := ResolutionAnswer.map_realizeSolution f
  map_residual := ResolutionAnswer.map_residual f

/-- The functorial Resolution map is exactly the map forced by relative
initiality. -/
theorem canonicalCompletionFunctorMap_isUniversal
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    canonicalCompletionFunctorMap f =
      canonicalCompletionMapOver f (canonicalCompletion T) := by
  exact canonicalCompletionMapOver_unique f (canonicalCompletion T)
    (canonicalCompletionFunctorMap f)

/-- Pointwise form: the universal map along `f` is exactly
`ResolutionAnswer.map f`. -/
theorem canonicalCompletionMapOver_eq_map
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (a : ResolutionAnswer S) :
    (canonicalCompletionMapOver f (canonicalCompletion T)).toFun a =
      ResolutionAnswer.map f a := by
  have h := canonicalCompletionFunctorMap_isUniversal f
  exact congrArg (fun q => q.toFun a) h.symm

/-- The canonical completion action respects identity translations. -/
theorem canonicalCompletionFunctor_id
    (S : Specification.{u}) :
    canonicalCompletionFunctorMap (SpecMorphism.id S) =
      CompletionHomOver.id (canonicalCompletion S) := by
  apply CompletionHomOver.ext
  intro a
  exact ResolutionAnswer.map_id S a

/-- The canonical completion action respects composition of specification
translations. -/
theorem canonicalCompletionFunctor_comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T) :
    canonicalCompletionFunctorMap (SpecMorphism.comp g f) =
      CompletionHomOver.comp
        (canonicalCompletionFunctorMap g)
        (canonicalCompletionFunctorMap f) := by
  apply CompletionHomOver.ext
  intro a
  exact ResolutionAnswer.map_comp g f a

/-- Universality gives an alternative proof of composition: both sides are maps
over the same composite base morphism, hence relative initiality forces them to
coincide. -/
theorem canonicalCompletionFunctor_comp_byUniversality
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T) :
    CompletionHomOver.comp
        (canonicalCompletionFunctorMap g)
        (canonicalCompletionFunctorMap f) =
      canonicalCompletionMapOver (SpecMorphism.comp g f)
        (canonicalCompletion U) := by
  exact canonicalCompletionMapOver_unique
    (SpecMorphism.comp g f)
    (canonicalCompletion U)
    (CompletionHomOver.comp
      (canonicalCompletionFunctorMap g)
      (canonicalCompletionFunctorMap f))

/-- Any structure-preserving isomorphisms from arbitrary completions to the
canonical completions force the naturality square to commute whenever the
source completion is universal. -/
theorem universalCompletion_naturalitySquare
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (A : CompletionObject S)
    (B : CompletionObject T)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual)
    (iS : CompletionIso A (canonicalCompletion S))
    (iT : CompletionIso B (canonicalCompletion T))
    (p : CompletionHomOver f A B) :
    CompletionHomOver.postcompVertical iT.hom p =
      CompletionHomOver.precompVertical
        (canonicalCompletionFunctorMap f) iS.hom := by
  rcases universalCompletion_relativeInitial
      f A (canonicalCompletion T) hA with
    ⟨q, hUnique⟩
  have hleft :
      CompletionHomOver.postcompVertical iT.hom p = q :=
    hUnique (CompletionHomOver.postcompVertical iT.hom p)
  have hright :
      CompletionHomOver.precompVertical
          (canonicalCompletionFunctorMap f) iS.hom = q :=
    hUnique (CompletionHomOver.precompVertical
      (canonicalCompletionFunctorMap f) iS.hom)
  exact hleft.trans hright.symm

/-- Coherent canonicity and naturality for universal completions.  Given
universal completions over `S` and `T`, there are unique canonical
isomorphisms, a unique map over every specification morphism `f`, and these
three unique pieces necessarily form the canonical naturality square. -/
theorem universalCompletions_canonicalNatural
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
              (canonicalCompletionFunctorMap f) iS.hom := by
  rcases universalCompletion_unique_iso S A hA with ⟨iS, hiS⟩
  rcases universalCompletion_unique_iso T B hB with ⟨iT, hiT⟩
  rcases universalCompletion_relativeInitial f A B hA with ⟨p, hp⟩
  refine ⟨iS, hiS, iT, hiT, p, hp, ?_⟩
  exact universalCompletion_naturalitySquare f A B hA iS iT p

/-- Strong Totality is therefore natural at the level of universal completion
objects: every specification morphism has a uniquely determined action between
canonical completions. -/
theorem strongTotality_universalNatural
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    Exists fun p : CompletionHomOver f
        (canonicalCompletion S) (canonicalCompletion T) =>
      forall q : CompletionHomOver f
          (canonicalCompletion S) (canonicalCompletion T),
        q = p :=
  canonicalCompletion_relativeInitial f (canonicalCompletion T)

end StrongTotality
end Resolution
