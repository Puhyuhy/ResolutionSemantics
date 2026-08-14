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
4. For finitely coded old carriers, generated Answers are residually finite
   with the stated whole-target bound. In the additional finite-signature
   subcase, the manuscript now identifies the qualitative conclusion as a
   consequence of classical ground-term recognizability; the explicit
   base-faithful bound and arbitrary-signature statement remain to be compared.
5. The embedded old image is closed under the generated total operations if
   and only if the old evaluator is total. Thus the genuinely partial case is
   not literally an inclusion of a closed finite-Rees-index subalgebra.
6. For finitely coded old carriers, the completion embedding is surjective
   exactly when the old evaluator is total.
7. Over an arbitrary carrier, an undefined old seed together with an
   old-fixing context is sufficient for proper completion, strict failure of
   equality at every finite stage, and unbounded separation rank.
8. The finite-base and old-fixing-context hypotheses are incomparable: the
   one-point algebra satisfies the former but not the latter, while natural
   arithmetic satisfies the latter but has no finite code for its carrier.
9. Natural and integer arithmetic instantiate the old-fixing criterion using
   0/0 and the context x maps to x + 0.

## Priority questions

- Is intrinsic finite-complement separation already known under another name?
- Has separation by homomorphisms into extensions with finite complement over
  a pointwise-fixed partial base been studied under a generalized Rees-index,
  relative residual-finiteness, or semigroup-separability formulation?
- Does classical ground-term recognizability also recover the manuscript's
  arbitrary-signature finite-base statement and comparable explicit
  base-faithful state bound, or only its finite-signature qualitative subcase?
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
