# Independent review guide

## Purpose

This package is intended for critical mathematical review, not endorsement.
Lean checks the formal derivations; it does not establish novelty, importance,
or the adequacy of the literature comparison.

## Central claims to inspect

1. Generated Answers form a normalized free compatible total extension of a
   binary partial algebra and admit the stated quotient presentation.
2. Distinct generated Answers can be separated by compatible total extensions
   whose genuine complement over the pointwise-preserved old carrier is
   finite. The canonical finite-tag presentation is derived rather than built
   into the primitive definition.
3. The finite observers induce a separated filtration and a complete
   observational completion with the stated equational conservativity.
4. For finitely coded old carriers, the completion embedding is surjective
   exactly when the old evaluator is total.
5. Over an arbitrary carrier, an undefined old seed together with an
   old-fixing context is sufficient for proper completion, strict failure of
   equality at every finite stage, and unbounded separation rank.
6. Natural and integer arithmetic instantiate that sufficient criterion using
   0/0 and the context x maps to x + 0.

## Priority questions

- Is intrinsic finite-complement separation already known under another name?
- Has separation by homomorphisms into extensions with finite complement over
  a pointwise-fixed base been studied in connection with finite Rees index,
  residual finiteness, or semigroup separability?
- Is the properness criterion known in an equivalent framework?
- Does the combined package contain a publishable contribution, and what
  literature or terminology is missing?

## Scope

The paper does not:

- claim to invent free completion, operation trees, or ultrametric completion;
- assign an ordinary number to division by zero;
- establish optimal separator complexity;
- prove Strong Totality;
- claim historical priority.

## Verification

Run:

    bash scripts/verify.sh
    bash scripts/build-paper.sh

The public declarations cited by the manuscript are listed in
[THEOREM_MAP.md](THEOREM_MAP.md). A concise critical response, including a
negative result or prior-art pointer, is explicitly welcome.

## Development disclosure

The manuscript and formalization were developed with substantial AI
assistance. Adrian Puha takes responsibility for the package and is requesting
independent human scrutiny before making publication claims.
