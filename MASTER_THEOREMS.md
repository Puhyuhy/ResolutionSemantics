# Master-theorem reduction research branch

Base commit: `67218af8cba8d61100288cd7f8422b7f3fa643da`

This branch records the post-audit reduction of the separation/completion story to two structural principles.

## I. Relative finite-complement realization

The checked result currently exposed is the pairwise theorem already proved as Theorem 3.3: every distinct generated pair can be separated by a compatible total extension that fixes the entire partial base pointwise and has only finitely many states outside that base.

The natural strengthening to test next is finite-pattern realization: for every finite set of generated Answers, build one observer that is injective on the whole selected finite subterm closure. The existing selected-subterm + sink construction strongly suggests this generalization, including for arbitrary finitary signatures, but this branch does not claim it until a Lean proof is added.

## II. Finite orbit compression => proper completion

The properness results are reorganized around a single dynamic mechanism. If every stage-m observer compresses the relevant unary orbit to a bounded finite state system, factorial sampling produces a Cauchy sequence. Pair-tailored finite-complement separators then rule out convergence to any generated Answer. Therefore the generated filtered space is incomplete and its completion embedding is not surjective.

Two existing hypotheses implement this mechanism:

1. **finite base:** the whole observer is finite;
2. **base-fixing context:** every base state is fixed, so only the finite complement can support nontrivial motion.

`lean/ResolutionMasterTheorems.lean` packages the already-checked consequences under this organization without changing their proofs.

## Sharper old-fixing bound to formalize

The current proof collapses the pointwise-fixed base to one settled state, producing an `(m+2)`-state quotient and the checked witness pair

`c_(m+2)!  ~_m  c_(m+3)!`.

There is a sharper direct argument that should be formalized separately:

- a stage-m observer has only `m+1` states outside the base (`m` tags plus overflow);
- if the orbit ever enters the base, it is fixed forever;
- otherwise the entire moving orbit remains in those at most `m+1` external states.

This suggests the stronger statement

`c_(m+1)!  ~_m  c_(m+2)!`,

whose `m = 0` instance subsumes the separate checked fact `c_1 ~_0 c_2`.

This strengthening is intentionally documented as a **research target**, not a theorem, until Lean and CI verify it.

## Intended end state

If the strengthening succeeds, the paper-facing architecture should become:

- Master I: relative finite-pattern realization;
- Master II: finite orbit compression implies proper completion;
- finite-base properness and old-fixing properness as corollaries;
- Theorem 3.3 as the two-point instance of Master I;
- the existing factorial mechanism explicitly credited as standard finite/profinite orbit technology.

This organization narrows the mathematical novelty claim while making the actual dependency structure cleaner and more reusable.
