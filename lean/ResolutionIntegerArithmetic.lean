import ResolutionFiniteTagProof

namespace Resolution
namespace IntegerArithmetic

/-- Integer arithmetic operations. Division is partial only on the old
    denominator zero; Resolution will totalize that case structurally. -/
inductive Op where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

/-- Signature of the concrete integer arithmetic realization. -/
abbrev signature : Resolution.Signature where
  Op := Op

/-- Old integer arithmetic. All primitive operations except division by zero
    are already defined. -/
def partialEval (f : Op) (a b : Int) : Option Int :=
  match f with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  | .div => if b = 0 then none else some (a / b)

/-- Concrete partial algebra over the integers. -/
abbrev alg : Resolution.PartialAlg signature where
  Carrier := Int
  eval := partialEval

@[simp] theorem partialEval_add (a b : Int) :
    partialEval Op.add a b = some (a + b) := by
  rfl

@[simp] theorem partialEval_sub (a b : Int) :
    partialEval Op.sub a b = some (a - b) := by
  rfl

@[simp] theorem partialEval_mul (a b : Int) :
    partialEval Op.mul a b = some (a * b) := by
  rfl

@[simp] theorem partialEval_div_zero (a : Int) :
    partialEval Op.div a 0 = none := by
  simp [partialEval]

@[simp] theorem partialEval_div_of_ne_zero
    (a b : Int) (hb : b ≠ 0) :
    partialEval Op.div a b = some (a / b) := by
  simp [partialEval, hb]

/-- Generated structured Answers for integer arithmetic. -/
abbrev Answer := Resolution.Free.GeneratedAns alg

/-- Embed an old integer into the generated Answer algebra. -/
def old (a : Int) : Answer :=
  Resolution.Free.generatedOld alg a

noncomputable def add (a b : Int) : Answer :=
  Resolution.Free.generatedOp alg Op.add (old a) (old b)

noncomputable def subtract (a b : Int) : Answer :=
  Resolution.Free.generatedOp alg Op.sub (old a) (old b)

noncomputable def multiply (a b : Int) : Answer :=
  Resolution.Free.generatedOp alg Op.mul (old a) (old b)

/-- Generated integer division. Denominator zero yields a structured Answer. -/
noncomputable def divide (a b : Int) : Answer :=
  Resolution.Free.generatedOp alg Op.div (old a) (old b)

@[simp] theorem old_val (a : Int) :
    (old a).1 = Resolution.RawAns.old a := by
  rfl

@[simp] theorem divide_val (a b : Int) :
    (divide a b).1 =
      Resolution.PartialAlg.liftOp alg Op.div
        (Resolution.RawAns.old a) (Resolution.RawAns.old b) := by
  rfl

/-- Old-defined addition is preserved exactly. -/
theorem add_normalizes (a b : Int) :
    add a b = old (a + b) := by
  simpa [add, old] using
    (Resolution.Free.generatedOp_old_of_defined
      alg Op.add a b (a + b) (partialEval_add a b))

/-- Old-defined subtraction is preserved exactly. -/
theorem subtract_normalizes (a b : Int) :
    subtract a b = old (a - b) := by
  simpa [subtract, old] using
    (Resolution.Free.generatedOp_old_of_defined
      alg Op.sub a b (a - b) (partialEval_sub a b))

/-- Old-defined multiplication is preserved exactly. -/
theorem multiply_normalizes (a b : Int) :
    multiply a b = old (a * b) := by
  simpa [multiply, old] using
    (Resolution.Free.generatedOp_old_of_defined
      alg Op.mul a b (a * b) (partialEval_mul a b))

/-- Integer division is unchanged whenever its old denominator is nonzero. -/
theorem divide_normalizes_of_ne_zero
    (a b : Int) (hb : b ≠ 0) :
    divide a b = old (a / b) := by
  simpa [divide, old] using
    (Resolution.Free.generatedOp_old_of_defined
      alg Op.div a b (a / b)
      (partialEval_div_of_ne_zero a b hb))

/-- Division by zero has an explicit suspended operation tree. -/
@[simp] theorem divide_zero_raw (a : Int) :
    (divide a 0).1 =
      Resolution.RawAns.susp Op.div
        (Resolution.RawAns.old a)
        (Resolution.RawAns.old (0 : Int)) := by
  rw [divide_val]
  rfl

/-- Read the old numerator from the left child of a singular Answer. -/
def leftOldValue : Resolution.RawAns signature Int -> Int
  | .old a => a
  | .susp _ (.old a) _ => a
  | .susp _ (.susp _ _ _) _ => 0

/-- Distinct integer numerators remain distinct after division by zero. -/
theorem divide_zero_injective :
    Function.Injective (fun a : Int => divide a 0) := by
  intro a b hab
  have hraw :
      Resolution.RawAns.susp Op.div
          (Resolution.RawAns.old a)
          (Resolution.RawAns.old (0 : Int)) =
        Resolution.RawAns.susp Op.div
          (Resolution.RawAns.old b)
          (Resolution.RawAns.old (0 : Int)) := by
    simpa only [divide_zero_raw] using congrArg Subtype.val hab
  have hnum := congrArg leftOldValue hraw
  simpa [leftOldValue] using hnum

/-- No generated division-by-zero Answer is an old integer. -/
theorem divide_zero_ne_old (a c : Int) :
    divide a 0 ≠ old c := by
  intro h
  have hraw := congrArg Subtype.val h
  rw [divide_zero_raw, old_val] at hraw
  cases hraw

/-- Distinguished generated `0 / 0` Answer. -/
noncomputable def zeroDivZero : Answer :=
  divide 0 0

@[simp] theorem zeroDivZero_raw :
    zeroDivZero.1 =
      Resolution.RawAns.susp Op.div
        (Resolution.RawAns.old (0 : Int))
        (Resolution.RawAns.old (0 : Int)) := by
  simpa [zeroDivZero] using divide_zero_raw 0

/-- Integer `0 / 0` and `1 / 0` are different Answers. -/
theorem zeroDivZero_ne_oneDivZero :
    zeroDivZero ≠ divide 1 0 := by
  intro h
  have hnum : (0 : Int) = 1 :=
    divide_zero_injective (by simpa [zeroDivZero] using h)
  have hne : (0 : Int) ≠ 1 := by decide
  exact hne hnum

/-- Generic observational completion specialized to integer arithmetic. -/
abbrev Completion :=
  Resolution.Filtered.Completion
    (Resolution.External.generatedFilteredSpace alg)

/-- Embed a generated integer Answer into the completion. -/
def embedAnswer (x : Answer) : Completion :=
  Resolution.Filtered.embed
    (Resolution.External.generatedFilteredSpace alg) x

/-- Embed an ordinary integer into the completed carrier. -/
def embedInt (a : Int) : Completion :=
  embedAnswer (old a)

noncomputable def completedAdd
    (q r : Completion) : Completion :=
  Resolution.External.completedGeneratedOp alg Op.add q r

noncomputable def completedSubtract
    (q r : Completion) : Completion :=
  Resolution.External.completedGeneratedOp alg Op.sub q r

noncomputable def completedMultiply
    (q r : Completion) : Completion :=
  Resolution.External.completedGeneratedOp alg Op.mul q r

/-- Completed integer division is a genuine total function. -/
noncomputable def completedDivide
    (q r : Completion) : Completion :=
  Resolution.External.completedGeneratedOp alg Op.div q r

/-- Completed operations extend their generated counterparts on old inputs. -/
theorem completedAdd_embedInt (a b : Int) :
    completedAdd (embedInt a) (embedInt b) =
      embedInt (a + b) := by
  calc
    completedAdd (embedInt a) (embedInt b) =
        embedAnswer (add a b) := by
      simpa [completedAdd, embedInt, embedAnswer, add, old] using
        (Resolution.External.completedGeneratedOp_embed
          alg Op.add
          (Resolution.Free.generatedOld alg a)
          (Resolution.Free.generatedOld alg b))
    _ = embedInt (a + b) := by
      rw [add_normalizes]
      rfl

/-- Completed subtraction preserves ordinary integer subtraction exactly. -/
theorem completedSubtract_embedInt (a b : Int) :
    completedSubtract (embedInt a) (embedInt b) =
      embedInt (a - b) := by
  calc
    completedSubtract (embedInt a) (embedInt b) =
        embedAnswer (subtract a b) := by
      simpa [completedSubtract, embedInt, embedAnswer, subtract, old] using
        (Resolution.External.completedGeneratedOp_embed
          alg Op.sub
          (Resolution.Free.generatedOld alg a)
          (Resolution.Free.generatedOld alg b))
    _ = embedInt (a - b) := by
      rw [subtract_normalizes]
      rfl

/-- Completed multiplication preserves ordinary integer multiplication. -/
theorem completedMultiply_embedInt (a b : Int) :
    completedMultiply (embedInt a) (embedInt b) =
      embedInt (a * b) := by
  calc
    completedMultiply (embedInt a) (embedInt b) =
        embedAnswer (multiply a b) := by
      simpa [completedMultiply, embedInt, embedAnswer, multiply, old] using
        (Resolution.External.completedGeneratedOp_embed
          alg Op.mul
          (Resolution.Free.generatedOld alg a)
          (Resolution.Free.generatedOld alg b))
    _ = embedInt (a * b) := by
      rw [multiply_normalizes]
      rfl

/-- Completed division extends generated division on old integers. -/
theorem completedDivide_embedInt (a b : Int) :
    completedDivide (embedInt a) (embedInt b) =
      embedAnswer (divide a b) := by
  simpa [completedDivide, embedInt, embedAnswer, divide, old] using
    (Resolution.External.completedGeneratedOp_embed
      alg Op.div
      (Resolution.Free.generatedOld alg a)
      (Resolution.Free.generatedOld alg b))

/-- Completed division agrees with ordinary integer division away from zero. -/
theorem completedDivide_of_ne_zero
    (a b : Int) (hb : b ≠ 0) :
    completedDivide (embedInt a) (embedInt b) =
      embedInt (a / b) := by
  calc
    completedDivide (embedInt a) (embedInt b) =
        embedAnswer (divide a b) :=
      completedDivide_embedInt a b
    _ = embedInt (a / b) := by
      simp [embedInt, divide_normalizes_of_ne_zero a b hb]

/-- Completed division by zero returns the embedded singular Answer. -/
theorem completedDivide_by_zero (a : Int) :
    completedDivide (embedInt a) (embedInt 0) =
      embedAnswer (divide a 0) :=
  completedDivide_embedInt a 0

/-- Ordinary integers embed injectively into the completed carrier. -/
theorem embedInt_injective : Function.Injective embedInt := by
  intro a b hab
  apply Resolution.Free.generatedOld_injective alg
  apply Resolution.Filtered.embed_injective
    (Resolution.External.generatedFilteredSpace alg)
  simpa [embedInt, embedAnswer, old] using hab

/-- Equality of embedded integers is exactly ordinary integer equality. -/
theorem embedInt_eq_iff (a b : Int) :
    embedInt a = embedInt b ↔ a = b := by
  constructor
  · intro h
    exact embedInt_injective h
  · intro h
    exact congrArg embedInt h

/-- A completed singular result is never an embedded old integer. -/
theorem completedDivide_zero_ne_old (a c : Int) :
    completedDivide (embedInt a) (embedInt 0) ≠ embedInt c := by
  intro h
  rw [completedDivide_by_zero] at h
  have hGenerated : divide a 0 = old c := by
    apply Resolution.Filtered.embed_injective
      (Resolution.External.generatedFilteredSpace alg)
    simpa [embedAnswer, embedInt] using h
  exact divide_zero_ne_old a c hGenerated

/-- Completed singular division remains injectively indexed by the numerator. -/
theorem completedDivide_zero_injective :
    Function.Injective
      (fun a : Int => completedDivide (embedInt a) (embedInt 0)) := by
  intro a b hab
  change completedDivide (embedInt a) (embedInt 0) =
      completedDivide (embedInt b) (embedInt 0) at hab
  rw [completedDivide_by_zero a, completedDivide_by_zero b] at hab
  apply divide_zero_injective
  apply Resolution.Filtered.embed_injective
    (Resolution.External.generatedFilteredSpace alg)
  simpa [embedAnswer] using hab

/-- Distinguished completed integer `0 / 0`. -/
noncomputable def completedZeroDivZero : Completion :=
  completedDivide (embedInt 0) (embedInt 0)

/-- Completed integer `0 / 0` lies outside the old integer image. -/
theorem completedZeroDivZero_ne_old (c : Int) :
    completedZeroDivZero ≠ embedInt c := by
  simpa [completedZeroDivZero] using completedDivide_zero_ne_old 0 c

/-- The completed integer carrier is nontrivial. -/
theorem completion_nontrivial :
    ∃ x y : Completion, x ≠ y := by
  refine ⟨embedInt 0, embedInt 1, ?_⟩
  intro h
  have h01 : (0 : Int) = 1 := embedInt_injective h
  have hne : (0 : Int) ≠ 1 := by decide
  exact hne h01

/-- Finite integer arithmetic expressions in the totalized carrier. -/
inductive Expr (V : Type) where
  | var : V -> Expr V
  | numeral : Int -> Expr V
  | add : Expr V -> Expr V -> Expr V
  | sub : Expr V -> Expr V -> Expr V
  | mul : Expr V -> Expr V -> Expr V
  | div : Expr V -> Expr V -> Expr V

namespace Expr

/-- Every expression node is evaluated by a total completed operation. -/
noncomputable def eval
    (rho : V -> Completion) : Expr V -> Completion
  | .var x => rho x
  | .numeral a => embedInt a
  | .add x y => completedAdd (eval rho x) (eval rho y)
  | .sub x y => completedSubtract (eval rho x) (eval rho y)
  | .mul x y => completedMultiply (eval rho x) (eval rho y)
  | .div x y => completedDivide (eval rho x) (eval rho y)

/-- Every finite integer arithmetic expression has an Answer. -/
theorem has_answer
    (rho : V -> Completion)
    (e : Expr V) :
    ∃ z : Completion, eval rho e = z :=
  ⟨eval rho e, rfl⟩

end Expr

end IntegerArithmetic
end Resolution
