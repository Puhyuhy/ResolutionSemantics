# Independent review guide

## Purpose

This package is intended for critical mathematical review, not endorsement.
Lean checks the formal derivations; it does not establish novelty, importance,
or the adequacy of the literature comparison.

The review package is version 1.2.0, dated 17 August 2026. Please identify the
reviewed commit when reporting results so comments remain reproducible.

## Central claims to inspect

1. The Diaconescu bridge correctly implements many-sorted finite-arity
   signatures with separate total and partial symbols, the Horn theory
   `Gamma`, `alpha`, `beta`, the satisfaction condition, `gamma`, recovery up
   to canonical equivalence, and the persistent-liberality lift. This is a
   verification/continuation claim, not a novelty claim for those results.
2. Generated Answers form a normalized free compatible total extension of a
   binary partial algebra and admit the stated quotient presentation.
3. Distinct generated Answers can be separated by compatible total extensions
   whose genuine complement over the pointwise-preserved old carrier is
   finite. The canonical finite-tag presentation is derived rather than built
   into the primitive definition.
4. The finite observers induce a separated filtration and a complete
   observational completion with the stated constant-bearing equational
   conservativity. Its relative universal property ranges over complete,
   separated filtered compatible total extensions with injective old
   embedding.
5. For finitely coded old carriers, generated Answers are residually finite
   with the stated whole-target bound. In the additional finite-signature
   subcase, the manuscript now identifies the qualitative conclusion as a
   consequence of classical ground-term recognizability; the explicit
   base-faithful bound and arbitrary-signature statement remain to be compared.
6. The embedded old image is closed under the generated total operations if
   and only if the old evaluator is total. Thus the genuinely partial case is
   not literally an inclusion of a closed finite-Rees-index subalgebra.
7. For finitely coded old carriers, the completion embedding is surjective
   exactly when the old evaluator is total.
8. Over an arbitrary carrier, an undefined old seed together with an
   old-fixing context is sufficient for proper completion, strict failure of
   equality at every finite stage, and unbounded separation rank.
9. The finite-base and old-fixing-context hypotheses are incomparable: the
   one-point algebra satisfies the former but not the latter, while natural
   arithmetic satisfies the latter but has no finite code for its carrier.
10. Natural and integer arithmetic instantiate the old-fixing criterion using
   0/0 and the context x maps to x + 0.

## Priority questions

- Does the concrete Lean statement of the Diaconescu bridge omit or alter any
  mathematically significant hypothesis? In particular, is canonical
  equivalence the right conservative replacement for definitional equality in
  the recovery statement?
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
    bash scripts/build-paper.sh --check-committed

The public declarations cited by the manuscript are listed in
[THEOREM_MAP.md](THEOREM_MAP.md). A concise critical response, including a
negative result or prior-art pointer, is explicitly welcome.

The axiom audit rejects proof holes and any dependency beyond `propext`,
`Classical.choice`, and `Quot.sound` in the principal theorem list.

## Development disclosure

The manuscript and formalization were developed with substantial AI
assistance. Adrian Puha takes responsibility for the package and is requesting
independent human scrutiny before making publication claims.
