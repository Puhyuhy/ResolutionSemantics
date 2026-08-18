import ResolutionFree

/-!
# Strong Totality: first formal layer

This module begins a research-only formalization of Strong Totality.

The first layer isolates the precise theorem already latent in the Resolution
kernel: every well-formed expression has one and only one Resolution answer.
Undefined old operations do not make evaluation fail; they are represented by
suspended answers.  Thus totality here is totality of *resolution*, not the
claim that the underlying partial algebra is total.

This is deliberately only the first layer of the broader Strong Totality
program.  No claim is made here yet about arbitrary meta-level specifications
or about expressions outside the syntax formalized by `Expr`.
-/

universe u v

namespace Resolution
namespace StrongTotality

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)

/-- `Resolves D e a` means that `a` is the Resolution answer of the
well-formed expression `e`. -/
def Resolves
    (e : Expr Sigma D.Carrier)
    (a : RawAns Sigma D.Carrier) : Prop :=
  Expr.res D e = a

/-- **Strong Totality, syntactic layer.** Every well-formed expression has a
Resolution answer. -/
theorem resolution_exists
    (e : Expr Sigma D.Carrier) :
    ∃ a : RawAns Sigma D.Carrier, Resolves D e a := by
  exact ⟨Expr.res D e, rfl⟩

/-- Resolution is deterministic: an expression cannot resolve to two different
raw answers. -/
theorem resolution_unique
    {e : Expr Sigma D.Carrier}
    {a b : RawAns Sigma D.Carrier}
    (ha : Resolves D e a)
    (hb : Resolves D e b) :
    a = b := by
  exact ha.symm.trans hb

/-- Canonical first formal statement of Strong Totality: every well-formed
expression has exactly one Resolution answer. -/
theorem strongTotality
    (e : Expr Sigma D.Carrier) :
    ∃! a : RawAns Sigma D.Carrier, Resolves D e a := by
  refine ⟨Expr.res D e, rfl, ?_⟩
  intro a ha
  exact ha.symm

/-- Package the canonical raw resolution as a generated Answer. -/
def answer
    (e : Expr Sigma D.Carrier) : Free.GeneratedAns D :=
  ⟨Expr.res D e, ⟨e, rfl⟩⟩

@[simp] theorem answer_val (a : D.Carrier) :
    answer D (.val a) =
      (⟨.old a, ⟨.val a, rfl⟩⟩ : Free.GeneratedAns D) := by
  rfl

/-- Application itself is total at the Resolution level: its answer is obtained
by resolving both arguments and applying `liftOp`. -/
@[simp] theorem answer_app
    (f : Sigma.Op)
    (l r : Expr Sigma D.Carrier) :
    (answer D (.app f l r)).1 =
      D.liftOp f (answer D l).1 (answer D r).1 := by
  rfl

/-- A defined old application resolves conservatively to the old result. -/
theorem defined_old_application
    (f : Sigma.Op) (a b c : D.Carrier)
    (h : D.eval f a b = some c) :
    (answer D (.app f (.val a) (.val b))).1 = .old c := by
  simp [answer, Expr.res, PartialAlg.liftOp, h]

/-- An undefined old application still has a Resolution answer: it becomes a
suspension rather than producing no answer. -/
theorem undefined_old_application
    (f : Sigma.Op) (a b : D.Carrier)
    (h : D.eval f a b = none) :
    (answer D (.app f (.val a) (.val b))).1 =
      .susp f (.old a) (.old b) := by
  simp [answer, Expr.res, PartialAlg.liftOp, h]

/-- Generated Answers are exactly answers of expressions: the canonical
resolution map onto `Free.GeneratedAns D` is surjective. -/
theorem answer_surjective :
    Function.Surjective (answer D) := by
  intro x
  rcases x.2 with ⟨e, he⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  exact he

/-- Equivalent existential form: every generated Answer has an expression that
resolves canonically to it. -/
theorem generated_has_source
    (x : Free.GeneratedAns D) :
    ∃ e : Expr Sigma D.Carrier, answer D e = x :=
  answer_surjective D x

end StrongTotality
end Resolution
