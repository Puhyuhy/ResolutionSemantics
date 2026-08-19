import ResolutionStrongTotalityExactness

/-!
# Rigidity and minimality of the Strong Totality completion

The universal property already shows that `ResolutionAnswer S` is a free
pointed extension of the ordinary solution type.  This module extracts a
stronger consequence useful for the foundational interpretation: there is no
room for hidden states in any universal pointed totalization.

Any universal totalization is not merely abstractly equivalent to the canonical
one.  Its carrier is exhausted by exactly two kinds of points: included
ordinary solutions and the distinguished residual point.  Moreover the
inclusion is injective and no included solution equals the residual.

Finally, the equivalence to the canonical completion is itself unique once it
is required to preserve ordinary solutions and the residual point.  This gives
a literal canonicity theorem, not merely existence of some abstract bijection.

Thus the canonical construction is minimal in a literal state-space sense: it
adds exactly one point and nothing else.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- In any universal pointed totalization, ordinary solutions remain distinct.
This follows by mapping universally into the canonical completion, where the
ordinary-solution inclusion is already known to be injective. -/
theorem universalTotalization_include_injective
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    Function.Injective includeSolution := by
  rcases hX (ResolutionAnswer S) (@realizeSolution S) .residual with
    ⟨toRA, hto, _⟩
  intro a b hab
  apply realizeSolution_injective
  calc
    realizeSolution a = toRA (includeSolution a) := (hto.1 a).symm
    _ = toRA (includeSolution b) := congrArg toRA hab
    _ = realizeSolution b := hto.1 b

/-- In any universal pointed totalization, no ordinary solution can collapse to
the distinguished residual point. -/
theorem universalTotalization_solution_ne_residual
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual)
    (x : Specification.Solution S) :
    includeSolution x ≠ residual := by
  rcases hX (ResolutionAnswer S) (@realizeSolution S) .residual with
    ⟨toRA, hto, _⟩
  intro h
  have himage :
      realizeSolution x =
        (ResolutionAnswer.residual : ResolutionAnswer S) := by
    calc
      realizeSolution x = toRA (includeSolution x) := (hto.1 x).symm
      _ = toRA residual := congrArg toRA h
      _ = (ResolutionAnswer.residual : ResolutionAnswer S) := hto.2
  exact realizeSolution_ne_residual x himage

/-- Strong constructive form of minimality: every point of an arbitrary
universal pointed totalization is forced to be either an included ordinary
solution or the unique residual point. -/
theorem universalTotalization_exhausted
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    forall z : X,
      (Exists fun x : Specification.Solution S => z = includeSolution x) ∨
      z = residual := by
  rcases hX (ResolutionAnswer S) (@realizeSolution S) .residual with
    ⟨toRA, hto, _⟩
  rcases resolutionAnswer_isUniversalTotalization S X includeSolution residual with
    ⟨fromRA, hfrom, _⟩
  have hleft : forall z : X, fromRA (toRA z) = z := by
    have hcompExt :
        ((forall x : Specification.Solution S,
            (fun q => fromRA (toRA q)) (includeSolution x) = includeSolution x) ∧
          (fun q => fromRA (toRA q)) residual = residual) := by
      constructor
      · intro x
        calc
          fromRA (toRA (includeSolution x)) = fromRA (realizeSolution x) :=
            congrArg fromRA (hto.1 x)
          _ = includeSolution x := hfrom.1 x
      · calc
          fromRA (toRA residual) = fromRA
              (ResolutionAnswer.residual : ResolutionAnswer S) :=
            congrArg fromRA hto.2
          _ = residual := hfrom.2
    have hidExt :
        ((forall x : Specification.Solution S,
            (fun q : X => q) (includeSolution x) = includeSolution x) ∧
          (fun q : X => q) residual = residual) :=
      ⟨fun _ => rfl, rfl⟩
    rcases hX X includeSolution residual with ⟨f, _, huniq⟩
    have hc : (fun q => fromRA (toRA q)) = f := huniq _ hcompExt
    have hi : (fun q : X => q) = f := huniq _ hidExt
    intro z
    exact congrFun (hc.trans hi.symm) z
  intro z
  cases hz : toRA z with
  | realized x hx =>
      let sx : Specification.Solution S := ⟨x, hx⟩
      left
      refine ⟨sx, ?_⟩
      calc
        z = fromRA (toRA z) := (hleft z).symm
        _ = fromRA (realizeSolution sx) := congrArg fromRA hz
        _ = includeSolution sx := hfrom.1 sx
  | residual =>
      right
      calc
        z = fromRA (toRA z) := (hleft z).symm
        _ = fromRA (ResolutionAnswer.residual : ResolutionAnswer S) :=
          congrArg fromRA hz
        _ = residual := hfrom.2

/-- The three rigidity properties together characterize the state-space shape
forced on every universal pointed totalization. -/
theorem universalTotalization_rigid
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    Function.Injective includeSolution ∧
      (forall x : Specification.Solution S, includeSolution x ≠ residual) ∧
      (forall z : X,
        (Exists fun x : Specification.Solution S => z = includeSolution x) ∨
        z = residual) := by
  exact ⟨
    universalTotalization_include_injective S X includeSolution residual hX,
    universalTotalization_solution_ne_residual S X includeSolution residual hX,
    universalTotalization_exhausted S X includeSolution residual hX
  ⟩

/-- Any universal totalization is canonically equivalent to `ResolutionAnswer S`:
there exists exactly one equivalence whose forward map sends every included
ordinary solution to its canonical realization and sends the distinguished
residual to the canonical residual. -/
theorem universalTotalization_unique_structural_equiv
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X)
    (hX : IsUniversalTotalization S X includeSolution residual) :
    Exists! e : Equiv X (ResolutionAnswer S),
      ((forall x : Specification.Solution S,
          e (includeSolution x) = realizeSolution x) ∧
        e residual = (ResolutionAnswer.residual : ResolutionAnswer S)) := by
  rcases hX (ResolutionAnswer S) (@realizeSolution S) .residual with
    ⟨toRA, hto, htoUnique⟩
  rcases resolutionAnswer_isUniversalTotalization S X includeSolution residual with
    ⟨fromRA, hfrom, _⟩
  have hleft : forall z : X, fromRA (toRA z) = z := by
    have hcompExt :
        ((forall x : Specification.Solution S,
            (fun q => fromRA (toRA q)) (includeSolution x) = includeSolution x) ∧
          (fun q => fromRA (toRA q)) residual = residual) := by
      constructor
      · intro x
        calc
          fromRA (toRA (includeSolution x)) = fromRA (realizeSolution x) :=
            congrArg fromRA (hto.1 x)
          _ = includeSolution x := hfrom.1 x
      · calc
          fromRA (toRA residual) = fromRA
              (ResolutionAnswer.residual : ResolutionAnswer S) :=
            congrArg fromRA hto.2
          _ = residual := hfrom.2
    have hidExt :
        ((forall x : Specification.Solution S,
            (fun q : X => q) (includeSolution x) = includeSolution x) ∧
          (fun q : X => q) residual = residual) :=
      ⟨fun _ => rfl, rfl⟩
    rcases hX X includeSolution residual with ⟨f, _, huniq⟩
    have hc : (fun q => fromRA (toRA q)) = f := huniq _ hcompExt
    have hi : (fun q : X => q) = f := huniq _ hidExt
    intro z
    exact congrFun (hc.trans hi.symm) z
  have hright : forall a : ResolutionAnswer S, toRA (fromRA a) = a := by
    intro a
    cases a with
    | realized x hx =>
        let sx : Specification.Solution S := ⟨x, hx⟩
        calc
          toRA (fromRA (.realized x hx)) =
              toRA (fromRA (realizeSolution sx)) := by rfl
          _ = toRA (includeSolution sx) := congrArg toRA (hfrom.1 sx)
          _ = realizeSolution sx := hto.1 sx
          _ = .realized x hx := by rfl
    | residual =>
        calc
          toRA (fromRA
              (ResolutionAnswer.residual : ResolutionAnswer S)) =
              toRA residual := congrArg toRA hfrom.2
          _ = (ResolutionAnswer.residual : ResolutionAnswer S) := hto.2
  let e : Equiv X (ResolutionAnswer S) := {
    toFun := toRA
    invFun := fromRA
    left_inv := hleft
    right_inv := hright
  }
  refine ⟨e, ?_, ?_⟩
  · exact hto
  · intro g hg
    have hgfun : g.toFun = toRA := by
      have hgf : g.toFun = toRA := by
        have htoSelf : toRA = toRA := rfl
        exact (htoUnique g.toFun hg).trans (htoUnique toRA hto).symm
      exact hgf
    apply Equiv.ext
    intro z
    exact congrFun hgfun z

/-- The canonical Strong Totality completion therefore contains no hidden
states: every answer is either a realized ordinary solution or the residual. -/
theorem strongTotality_master_minimal_exhaustion
    (S : Specification.{u}) :
    forall a : ResolutionAnswer S,
      (Exists fun x : Specification.Solution S => a = realizeSolution x) ∨
      a = (ResolutionAnswer.residual : ResolutionAnswer S) := by
  intro a
  cases a with
  | realized x hx =>
      exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  | residual =>
      exact Or.inr rfl

end StrongTotality
end Resolution
