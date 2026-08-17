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

`lean/ResolutionMasterTheorems.lean` packages the checked consequences under this organization.

## Verified sharper old-fixing bound

The original proof collapsed the pointwise-fixed base to one settled state, producing an `(m+2)`-state quotient and the witness pair

`c_(m+2)!  ~_m  c_(m+3)!`.

The research branch now contains a Lean-checked sharper proof in
`lean/ResolutionOldFixingContextSharperOrbit.lean`.

A stage-m observer has only `m+1` states outside the base (`m` tags plus overflow). The proof splits an observer orbit into two exhaustive cases:

- if the orbit enters the base, the base-fixing law makes it constant forever;
- otherwise the orbit remains in the `m+1` external states, so a repetition occurs by pigeonhole and its period divides `(m+1)!`.

Consequently the stronger statement is formally verified:

`c_(m+1)!  ~_m  c_(m+2)!`.

The public research API exposes both this stage-equivalence theorem and the resulting strict separation-rank bound

`m < rank(c_(m+1)!, c_(m+2)!)`.

The `m = 0` instance yields `c_1 ~_0 c_2`, so the former separate stage-zero phenomenon is subsumed by the sharper general orbit theorem.

## Current end state

The branch now supports the following architecture:

- Master I: pairwise relative finite-complement realization, with finite-pattern realization still the next strengthening to test;
- Master II: finite orbit compression implies proper completion;
- finite-base properness and old-fixing properness as instances of the dynamic mechanism;
- the old-fixing unbounded-rank witness sharpened from `(m+2)!/(m+3)!` to `(m+1)!/(m+2)!`;
- the factorial mechanism explicitly treated as standard finite/profinite orbit technology rather than a novelty claim.

This organization narrows the mathematical novelty claim while making the actual dependency structure cleaner and more reusable.
