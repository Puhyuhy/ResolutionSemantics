# Independent review guide

## Purpose

This package is intended for critical mathematical review, not endorsement.
Lean checks the formal derivations; it does not establish novelty, importance,
or the adequacy of the literature comparison.

The review package is version 1.2.0, manuscript revision dated 18 August 2026.
Please identify the reviewed commit when reporting results so comments remain
reproducible.

## Central claims to inspect

1. **Free-completion substrate.** Generated Answers form the stated normalized
   free compatible total extension of a binary partial algebra and admit the
   quotient presentation by equality after resolution. This is infrastructure,
   not a novelty claim.
2. **Relative observer class.** Intrinsic finite-complement observers preserve
   the partial base pointwise and budget only genuinely outside states. The base
   itself may be infinite. The canonical finite-tag presentation is derived
   from this observer class rather than built into its primitive definition.
3. **Master I — finite-pattern realization.** For any finite family of generated
   Answers, one compatible finite-complement observer is simultaneously
   injective on the whole family. Pairwise finite-tag separation should follow
   as the two-point case, while the explicit pairwise constructor-size bound is
   retained by the older quantitative separator.
4. **Observational filtration.** The finite observers induce a separated
   filtration and complete Cauchy completion with the stated relative extension
   property and exact constant-bearing equational conservativity.
5. **Master II — trajectory compression.** The factorial Cauchy theorem should
   require only a finite code of the single relevant deterministic observer
   trajectory at each stage, not finiteness of the whole observer carrier. The
   proof should reduce to standard finite periodicity and factorial
   synchronization; this component is not claimed as new.
6. **Finite-pattern escape.** For a growing unary syntax
   `t_(k+1) = susp(u,t_k,old(e))`, the selected candidate/prefix observer should
   realize the finite pattern exactly, force the next unseen iterate into
   overflow, and keep the remaining tail in overflow. This should rule out
   convergence to every finite generated candidate without using the finite-
   state periodicity argument.
7. **Combined properness theorem.** Trajectory compression supplies the Cauchy
   half and finite-pattern escape supplies the no-generated-limit half; together
   they force a proper observational completion. Review whether this is a
   genuine structural unification rather than merely a repackaging of two
   unrelated proofs.
8. **Finite-base instance.** For finitely coded old carriers, the completion
   embedding is surjective exactly when the old evaluator is total. Check that
   this is correctly obtained as an instance of the combined mechanism when an
   undefined application exists.
9. **Infinite-base old-fixing instance.** An undefined old seed together with a
   pointwise old-fixing unary context should provide both trajectory compression
   and finite-pattern escape over an arbitrary, possibly infinite base. The
   sharp checked witness is `c_(n+1)! ~_n c_(n+2)!`, yielding unbounded least
   finite-tag separation rank.
10. **Arithmetic instances.** Natural and integer arithmetic instantiate the
    old-fixing criterion using `0/0` and `x ↦ x + 0`, while division by zero
    remains a structured non-old Answer rather than an ordinary number.
11. **Diaconescu provenance bridge.** The many-sorted finite-arity formalization
    should correctly implement the operations-only fragment used by the paper:
    separate total and partial symbols, `Gamma`, `alpha`, `beta`, the
    satisfaction condition, `gamma`, recovery up to canonical equivalence,
    persistent liberality, the hom-set adjunction laws, semantic consequence,
    fixed-signature initiality transfers, and the singleton-sort binary
    specialization. This is a verification/continuation claim, not a novelty
    claim for Diaconescu's results.

## Priority novelty questions

- Is simultaneous finite-pattern realization over a pointwise-preserved,
  possibly infinite partial base already known under another formulation?
- Has separation by extensions whose complement over such a fixed partial base
  is finite been studied as relative residual finiteness, generalized Rees
  index, or another separability notion?
- Is the **compression–escape interaction** known in an equivalent framework:
  finite complexity of the relevant observer trajectory making a factorial
  sample Cauchy while candidate-tailored finite-pattern observers force escape
  from every finite generated candidate?
- Does classical ground-term recognizability recover only the finite-signature
  qualitative finite-base residual-finiteness consequence, or can it also
  recover the relative base-faithful finite-pattern statement and explicit
  state-budget behavior?
- Is the exact finite-base properness criterion known in a comparable relative
  completion framework?
- Is there an existing arbitrary-base theorem subsuming the old-fixing
  compression–escape instance?
- Does the combined package contain a publishable contribution, and what
  literature or terminology is still missing?

## Priority formalization questions

- Does `ResolutionSemantics.MasterTheorems.relativeFinitePatternRealization`
  state exactly the finite-pattern result described in the manuscript?
- Does `ObserverOrbitCompression` constrain only the relevant trajectory, as
  claimed, rather than smuggling in global finiteness?
- Does `finitePatternEscapeNoGeneratedLimit` genuinely derive nonconvergence
  from selected-pattern/overflow mechanics rather than restating
  nonconvergence as an assumption?
- Do the finite-base and old-fixing instances both factor through
  `compressedEscapingOrbitNotComplete` / the corresponding embedding theorem?
- Is the sharper `(n+1)!/(n+2)!` old-fixing indexing correct at stage `n`,
  including the `n = 0` case?
- Does the Diaconescu binary specialization commute with the data operation,
  existence equality, and truth constant in both directions?
- Do the initiality and semantic-consequence results have exactly the
  fixed-signature, operations-only and universe-bounded scope stated by the
  manuscript?

## Scope and non-claims

The paper does not:

- claim to invent free compatible completion, operation trees, selected-subterm
  sink constructions in isolation, finite-state eventual periodicity,
  factorial synchronization, or generic Cauchy completion;
- claim Diaconescu's encoding or adjunction theory as new;
- assign an ordinary number to division by zero;
- establish optimal separator complexity;
- give a necessary-and-sufficient arbitrary-infinite-base properness criterion;
- extend the full observational completion theory to arbitrary many-sorted
  signatures;
- prove Strong Totality;
- formalize the full institution/comorphism layer or arbitrary signature
  morphisms;
- claim historical priority.

## Verification

Run:

    bash scripts/verify.sh
    bash scripts/build-paper.sh --check-committed

The public declarations cited by the manuscript are organized in
[THEOREM_MAP.md](THEOREM_MAP.md). The research reduction behind the manuscript
architecture is summarized in [MASTER_THEOREMS.md](MASTER_THEOREMS.md).

The axiom audit rejects proof holes and any dependency beyond `propext`,
`Classical.choice`, and `Quot.sound` in the principal theorem list.

A concise critical response, including a negative result, counterexample, or
prior-art pointer, is explicitly welcome.

## Development disclosure

The manuscript and formalization were developed with substantial AI
assistance. Adrian Puha takes responsibility for the package and is requesting
independent human scrutiny before making publication claims.
