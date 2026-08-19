import ResolutionFree

/-!
# Strong Totality for arbitrary mathematical specifications

This module formalizes the intended Strong Totality principle itself, rather
than merely the already-total syntax evaluator `Expr.res`.

A *well-formed mathematical specification* is represented extensionally by a
type of candidate answers together with a predicate saying which candidates
satisfy the specification