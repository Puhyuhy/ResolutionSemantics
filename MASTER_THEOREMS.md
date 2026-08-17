# Master-theorem reduction research branch

Base commit: `67218af8cba8d61100288cd7f8422b7f3fa643da`

This branch records the post-audit reduction of the separation/completion story to two structural principles.

## I. Relative finite-pattern realization

The pairwise separator of Theorem 3.3 has now been generalized and Lean-checked.

For any finite list of generated Answers, `lean/ResolutionFinitePatternRealization.lean` forms the union of their finite subterm closures and constructs one compatible finite-tag observer that:

- fixes the entire partial base pointwise;
- gives selected suspended nodes first-occurrence finite tags;
- sends unrelated transitions to one overflow state;
- evaluates every selected normal node to its encoding;
- is injective simultaneously on all generated Answers in the chosen finite list.

Thus pairwise finite-tag separation is the two-point instance of a stronger finite-pattern theorem. The public API is `lean/ResolutionFinitePatternRealizationPublic.lean`, and `ResolutionMasterTheorems.relativeFinitePatternRealization` exposes it as Master I.

This result is currently formalized for the repository's one-sorted binary presentation. Generalization to arbitrary finitary signatures remains a distinct further test; it is not claimed by this branch yet.

## II. Finite orbit compression => proper completion

The properness results are reorganized around a single dynamic mechanism. If every stage-m observer compresses the relevant unary orbit to a bounded finite state system, factorial sampling produces a Cauchy sequence. Pair-tailored finite-complement separators then rule out convergence to any generated Answer. Therefore the generated filtered space is incomplete and its completion embedding is not surjective.

Two existing hypotheses implement this mechanism:

1. **finite base:** the whole observer is finite;
2. **base-fixing context:** every base state is fixed, so only the finite complement can support nontrivial motion.

`lean/ResolutionMasterTheorems.lean` packages the checked consequences under this organization.

## Verified sharper old-fixing bound

The original proof collapsed the pointwise-fixed base to one settled state, producing an `(m+2)`-state quotient and the witness pair

`c_(m+2)!  ~_m  c_(m+3)!`.

The research branch now contains a Lean-checked sharper proof in `lean/ResolutionOldFixingContextSharperOrbit.lean`.

A stage-m observer has only `m+1` states outside the base (`m` tags plus overflow). The proof splits an observer orbit into two exhaustive cases:

- if the orbit enters the base, the base-fixing law makes it constant forever;
- otherwise the orbit remains in the `m+1` external states, so a repetition occurs by pigeonhole and its period divides `(m+1)!`.

Consequently the stronger statement is formally verified:

`c_(m+1)!  ~_m  c_(m+2)!`.

The public research API exposes both this stage-equivalence theorem and the resulting strict separation-rank bound

`m < rank(c_(m+1)!, c_(m+2)!)`.

The `m = 0` instance yields `c_1 ~_0 c_2`, so the former separate stage-zero phenomenon is subsumed by the sharper general orbit theorem.

## Current end state

The branch now supports the following checked architecture:

- **Master I:** one finite-complement observer simultaneously realizes every chosen finite pattern of generated Answers;
- Theorem 3.3's pairwise finite-tag statement is the two-point consequence of Master I;
- **Master II:** finite orbit compression supplies the proper-completion mechanism;
- finite-base properness and old-fixing properness are instances of the dynamic mechanism;
- the old-fixing unbounded-rank witness is sharpened from `(m+2)!/(m+3)!` to `(m+1)!/(m+2)!`;
- the factorial mechanism is explicitly treated as standard finite/profinite orbit technology rather than a novelty claim.

The main unresolved reduction test is now whether Master I can be lifted from the concrete binary presentation to an arbitrary finitary signature without introducing any genuinely new obstruction. That test will determine how much of the remaining structure is presentation-specific.
