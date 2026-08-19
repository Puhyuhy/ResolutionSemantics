import ResolutionStrongTotalityMinimalSection

/-!
# Universal completion category for Strong Totality

Fix a well-formed mathematical specification `S`.  A pointed completion of `S`
consists of a carrier of generalized answers, an embedding of every ordinary
certified solution, and one distinguished residual point.  Morphisms preserve
both the ordinary solutions and the residual point.

The canonical `ResolutionAnswer S` construction is initial in this category:
for every pointed completion there exists exactly one structure-preserving map
from `ResolutionAnswer S` into it.  This packages the previously proved fold
principle as a categorical universal property and makes the word "completion"
representation-independent.

Strong Totality then appears as a consequence of the universal completion
operator: the carrier of the canonical completion is always inhabited by its
residual point, while ordinary solutions embed conservatively when present.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- A pointed completion of a specification. -/
structure CompletionObject (S : Specification.{u}) where
  Carrier : Type u
  includeSolution : Specification.Solution S -> Carrier
  residual : Carrier

/-- A morphism of completions preserves all ordinary solutions and the residual
point. -/
structure CompletionHom
    {S : Specification.{u}}
    (A B : CompletionObject S) where
  toFun : A.Carrier -> B.Carrier
  map_solution : forall x : Specification.Solution S,
    toFun (A.includeSolution x) = B.includeSolution x
  map_residual : toFun A.residual = B.residual

namespace CompletionHom

/-- Identity completion morphism. -/
def id
    {S : Specification.{u}}
    (A : CompletionObject S) : CompletionHom A A where
  toFun := fun x => x
  map_solution := fun _ => rfl
  map_residual := rfl

/-- Composition of completion morphisms. -/
def comp
    {S : Specification.{u}}
    {A B C : CompletionObject S}
    (g : CompletionHom B C)
    (f : CompletionHom A B) : CompletionHom A C where
  toFun := fun x => g.toFun (f.toFun x)
  map_solution := by
    intro x
    rw [f.map_solution x, g.map_solution x]
  map_residual := by
    rw [f.map_residual, g.map_residual]

@[simp] theorem id_apply
    {S : Specification.{u}}
    (A : CompletionObject S)
    (x : A.Carrier) :
    (id A).toFun x = x := by
  rfl

@[simp] theorem comp_apply
    {S : Specification.{u}}
    {A B C : CompletionObject S}
    (g : CompletionHom B C)
    (f : CompletionHom A B)
    (x : A.Carrier) :
    (comp g f).toFun x = g.toFun (f.toFun x) := by
  rfl

/-- Extensionality for completion morphisms. -/
theorem ext
    {S : Specification.{u}}
    {A B : CompletionObject S}
    (f g : CompletionHom A B)
    (h : forall x : A.Carrier, f.toFun x = g.toFun x) :
    f = g := by
  cases f with
  | mk fto fsol fres =>
      cases g with
      | mk gto gsol gres =>
          have hfun : fto = gto := by
            funext x
            exact h x
          cases hfun
          rfl

@[simp] theorem comp_id
    {S : Specification.{u}}
    {A B : CompletionObject S}
    (f : CompletionHom A B) :
    comp (id B) f = f := by
  apply ext
  intro x
  rfl

@[simp] theorem id_comp
    {S : Specification.{u}}
    {A B : CompletionObject S}
    (f : CompletionHom A B) :
    comp f (id A) = f := by
  apply ext
  intro x
  rfl

@[simp] theorem comp_assoc
    {S : Specification.{u}}
    {A B C D : CompletionObject S}
    (h : CompletionHom C D)
    (g : CompletionHom B C)
    (f : CompletionHom A B) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  intro x
  rfl

end CompletionHom

/-- An isomorphism of pointed completions, expressed without importing any
external category-theory library. -/
structure CompletionIso
    {S : Specification.{u}}
    (A B : CompletionObject S) where
  hom : CompletionHom A B
  inv : CompletionHom B A
  hom_inv_id : CompletionHom.comp inv hom = CompletionHom.id A
  inv_hom_id : CompletionHom.comp hom inv = CompletionHom.id B

namespace CompletionIso

/-- Completion isomorphisms are determined by their two structure-preserving
maps; the inverse-law fields are propositions. -/
theorem ext
    {S : Specification.{u}}
    {A B : CompletionObject S}
    (e f : CompletionIso A B)
    (hhom : e.hom = f.hom)
    (hinv : e.inv = f.inv) :
    e = f := by
  cases e
  cases f
  cases hhom
  cases hinv
  rfl

end CompletionIso

/-- The canonical Resolution completion of a specification. -/
def canonicalCompletion
    (S : Specification.{u}) : CompletionObject S where
  Carrier := ResolutionAnswer S
  includeSolution := realizeSolution
  residual := .residual

/-- The unique candidate morphism from the canonical completion into any other
pointed completion. -/
def canonicalCompletionMap
    {S : Specification.{u}}
    (A : CompletionObject S) :
    CompletionHom (canonicalCompletion S) A where
  toFun := ResolutionAnswer.fold A.includeSolution A.residual
  map_solution := by
    intro x
    cases x
    rfl
  map_residual := rfl

/-- The canonical Resolution completion is initial among all pointed
completions of the same mathematical specification. -/
theorem canonicalCompletion_initial
    (S : Specification.{u})
    (A : CompletionObject S) :
    Exists fun f : CompletionHom (canonicalCompletion S) A =>
      forall g : CompletionHom (canonicalCompletion S) A, g = f := by
  refine ⟨canonicalCompletionMap A, ?_⟩
  intro g
  apply CompletionHom.ext
  intro a
  cases a with
  | realized x hx =>
      have h := g.map_solution (⟨x, hx⟩ : Specification.Solution S)
      simpa [canonicalCompletion, realizeSolution, canonicalCompletionMap] using h
  | residual =>
      simpa [canonicalCompletion, canonicalCompletionMap] using g.map_residual

/-- Existence of the unique universal map in direct form. -/
theorem canonicalCompletion_map_unique
    {S : Specification.{u}}
    (A : CompletionObject S)
    (g : CompletionHom (canonicalCompletion S) A) :
    g = canonicalCompletionMap A := by
  rcases canonicalCompletion_initial S A with ⟨f, huniq⟩
  have hg : g = f := huniq g
  have hc : canonicalCompletionMap A = f := huniq (canonicalCompletionMap A)
  exact hg.trans hc.symm

/-- The earlier predicate `IsUniversalTotalization` is exactly satisfied by the
carrier data of the canonical completion. -/
theorem canonicalCompletion_universal
    (S : Specification.{u}) :
    IsUniversalTotalization S
      (canonicalCompletion S).Carrier
      (canonicalCompletion S).includeSolution
      (canonicalCompletion S).residual :=
  resolutionAnswer_isUniversalTotalization S

/-- Any pointed completion whose carrier already satisfies the universal fold
property receives mutually inverse structure-preserving maps to and from the
canonical Resolution completion. -/
theorem universalCompletion_has_inverse_maps
    (S : Specification.{u})
    (A : CompletionObject S)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual) :
    Exists fun toCanonical : CompletionHom A (canonicalCompletion S) =>
      Exists fun fromCanonical : CompletionHom (canonicalCompletion S) A =>
        (forall x : A.Carrier,
          fromCanonical.toFun (toCanonical.toFun x) = x) ∧
        (forall a : ResolutionAnswer S,
          toCanonical.toFun (fromCanonical.toFun a) = a) := by
  rcases hA (ResolutionAnswer S) (@realizeSolution S) .residual with
    ⟨toRA, hto, _⟩
  let toCanonical : CompletionHom A (canonicalCompletion S) := {
    toFun := toRA
    map_solution := hto.1
    map_residual := hto.2
  }
  let fromCanonical : CompletionHom (canonicalCompletion S) A :=
    canonicalCompletionMap A
  refine ⟨toCanonical, fromCanonical, ?_, ?_⟩
  · have hcomp : CompletionHom.comp fromCanonical toCanonical = CompletionHom.id A := by
      let compHom := CompletionHom.comp fromCanonical toCanonical
      have hExt :
          ((forall x : Specification.Solution S,
              compHom.toFun (A.includeSolution x) = A.includeSolution x) ∧
            compHom.toFun A.residual = A.residual) := by
        exact ⟨compHom.map_solution, compHom.map_residual⟩
      have hidExt :
          ((forall x : Specification.Solution S,
              (fun z : A.Carrier => z) (A.includeSolution x) = A.includeSolution x) ∧
            (fun z : A.Carrier => z) A.residual = A.residual) := by
        exact ⟨fun _ => rfl, rfl⟩
      rcases hA A.Carrier A.includeSolution A.residual with ⟨f, _, huniq⟩
      have hc : compHom.toFun = f := huniq compHom.toFun hExt
      have hi : (fun z : A.Carrier => z) = f := huniq (fun z => z) hidExt
      apply CompletionHom.ext
      intro x
      exact congrFun (hc.trans hi.symm) x
    intro x
    exact congrArg (fun k => k.toFun x) hcomp
  · have hc : CompletionHom.comp toCanonical fromCanonical =
        canonicalCompletionMap (canonicalCompletion S) :=
      canonicalCompletion_map_unique
        (canonicalCompletion S)
        (CompletionHom.comp toCanonical fromCanonical)
    have hi : CompletionHom.id (canonicalCompletion S) =
        canonicalCompletionMap (canonicalCompletion S) :=
      canonicalCompletion_map_unique
        (canonicalCompletion S)
        (CompletionHom.id (canonicalCompletion S))
    have hcomp : CompletionHom.comp toCanonical fromCanonical =
        CompletionHom.id (canonicalCompletion S) :=
      hc.trans hi.symm
    intro a
    exact congrArg (fun k => k.toFun a) hcomp

/-- Every universal pointed completion is uniquely isomorphic, as a pointed
completion, to the canonical `ResolutionAnswer` completion.  This is the
categorical canonicity form of Strong Totality: not only the carrier type but
the solution embedding and residual point are fixed up to one unique
structure-preserving isomorphism. -/
theorem universalCompletion_unique_iso
    (S : Specification.{u})
    (A : CompletionObject S)
    (hA : IsUniversalTotalization S A.Carrier A.includeSolution A.residual) :
    Exists fun i : CompletionIso A (canonicalCompletion S) =>
      forall j : CompletionIso A (canonicalCompletion S), j = i := by
  rcases universalCompletion_has_inverse_maps S A hA with
    ⟨toCanonical, fromCanonical, hleft, hright⟩
  have hleftHom :
      CompletionHom.comp fromCanonical toCanonical = CompletionHom.id A := by
    apply CompletionHom.ext
    intro x
    exact hleft x
  have hrightHom :
      CompletionHom.comp toCanonical fromCanonical =
        CompletionHom.id (canonicalCompletion S) := by
    apply CompletionHom.ext
    intro a
    exact hright a
  let i : CompletionIso A (canonicalCompletion S) := {
    hom := toCanonical
    inv := fromCanonical
    hom_inv_id := hleftHom
    inv_hom_id := hrightHom
  }
  refine ⟨i, ?_⟩
  intro j
  have hhom : j.hom = toCanonical := by
    rcases hA (ResolutionAnswer S) (@realizeSolution S) .residual with
      ⟨f, _, huniq⟩
    have hjPres :
        ((forall x : Specification.Solution S,
            j.hom.toFun (A.includeSolution x) = realizeSolution x) ∧
          j.hom.toFun A.residual =
            (ResolutionAnswer.residual : ResolutionAnswer S)) := by
      constructor
      · intro x
        change j.hom.toFun (A.includeSolution x) = realizeSolution x
        exact j.hom.map_solution x
      · change j.hom.toFun A.residual =
          (ResolutionAnswer.residual : ResolutionAnswer S)
        exact j.hom.map_residual
    have hiPres :
        ((forall x : Specification.Solution S,
            toCanonical.toFun (A.includeSolution x) = realizeSolution x) ∧
          toCanonical.toFun A.residual =
            (ResolutionAnswer.residual : ResolutionAnswer S)) := by
      constructor
      · intro x
        change toCanonical.toFun (A.includeSolution x) = realizeSolution x
        exact toCanonical.map_solution x
      · change toCanonical.toFun A.residual =
          (ResolutionAnswer.residual : ResolutionAnswer S)
        exact toCanonical.map_residual
    have hj : j.hom.toFun = f := huniq j.hom.toFun hjPres
    have hi : toCanonical.toFun = f := huniq toCanonical.toFun hiPres
    apply CompletionHom.ext
    intro x
    exact congrFun (hj.trans hi.symm) x
  have hinv : j.inv = fromCanonical := by
    have hj := canonicalCompletion_map_unique A j.inv
    have hi := canonicalCompletion_map_unique A fromCanonical
    exact hj.trans hi.symm
  apply CompletionIso.ext
  · change j.hom = toCanonical
    exact hhom
  · change j.inv = fromCanonical
    exact hinv

/-- Strong Totality follows immediately from the canonical completion object:
its carrier is always inhabited by its distinguished residual point. -/
theorem strongTotality_fromCanonicalCompletion
    (S : Specification.{u}) :
    Nonempty (canonicalCompletion S).Carrier := by
  exact ⟨(canonicalCompletion S).residual⟩

/-- Ordinary certified solutions are preserved injectively inside the canonical
completion. -/
theorem canonicalCompletion_conservative
    (S : Specification.{u}) :
    Function.Injective (canonicalCompletion S).includeSolution :=
  realizeSolution_injective

end StrongTotality
end Resolution
