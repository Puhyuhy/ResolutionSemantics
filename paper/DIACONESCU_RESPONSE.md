# Paper I — presentation pass in response to specialist feedback

Branch: `readability/diaconescu-response` (branched from `main`; `main` untouched).

Complementary to `rewrite/paper1-academic-rebuild`, which rebuilds the paper
from statements and proofs. This branch does the cheaper, orthogonal job:
it repairs the **presentation layer** so the mathematics already in the
manuscript becomes visible. The two can be merged or one can supersede
the other; nothing here conflicts with `EDITORIAL_GUARDRAILS.md`.

## The feedback, stripped of polemic

Three actionable signals:

1. **"Almost unreadable by scientific community standards."** No detail given.
   This is the blocker, and it is about presentation, not about the theorems.
2. **Formal proofs are not of interest; proofs exist to support understanding.**
   Lean must not be load-bearing in the presentation.
3. **The informal→formal gap cannot be audited by a reader.** Correct, and
   granted even by proof-assistant advocates. The human proofs must stand alone.

Note the reviewer's position: he works in institution theory and algebraic
specification and has co-authored with Goguen. He is precisely the community
that owns the word *observational*, and he is the author of the encoding the
manuscript formalizes. Both facts were being handled badly (see 3 and 5 below).

## Diagnosis

Six concrete defects, all fixable without touching the mathematics.

**1. No example anywhere before Section 6.** The introduction ran six pages of
abstraction — "compatible total extension", "separated filtration",
"candidate-tailored finite-pattern observer" — before the reader met a single
concrete object. A specialist skimming has nothing to hold. This alone explains
a bounce.

**2. Twelve defensive disclaimers.** "we do not claim novelty for that
substrate", "is not claimed as new", "not a third novelty claim", "background
or compatibility layers rather than independent novelty claims", and so on. The
paper was organized around defending a priority claim rather than explaining a
mathematical situation. A referee is not adjudicating priority; the hedging
reads as low confidence and forces him to reconstruct the mathematics from
between the disclaimers.

**3. `observational` used without disambiguation.** The term is taken in
algebraic specification (behavioural/observational satisfaction, Bidoit–
Hennicker, Sannella–Tarlecki, hidden algebra). Using it undefined in front of
that community reads as either confusion or unacknowledged appropriation.

**4. Lean in the shop window.** In the title, ~20% of the abstract, a paragraph
of the introduction, four fully-qualified identifiers *in the introduction*,
and 40 inline references through the body. An identifier such as
`ResolutionSemantics.MasterTheorems.finitePatternEscapeNoGeneratedLimit` in a
mathematics introduction is an implementation detail in the display case.

**5. The encoding section was the worst own-goal.** It was titled "A
Lean-Checked Bridge to Diaconescu's Encoding" and framed as "supporting
provenance, not a third novelty claim" — i.e. as a proof-assistant exercise on
the reviewer's own theorem, sent to the reviewer. Its actual mathematical
content is a *localization*: the construction is the singleton-sort binary case
of the standard encoding. That is worth stating; the framing was not.

**6. Three-clause title**, the third clause being the Lean one.

## Changes made

| Area | Before | After |
|---|---|---|
| Title | 3 clauses, Lean in the third | 2 clauses, no Lean |
| Abstract | ~400 words, 3 disclaimers, Lean paragraph | ~200 words, states both theorems, carries the worked example, no disclaimers |
| Introduction | abstraction first, 4 Lean identifiers, no example | opens with the `ℕ`, `0/0`, `x ↦ x+0` example; notation table; `observational` disambiguated in a remark; zero Lean |
| Body | 40 inline Lean references | 0; all 40 collected into an appendix theorem map, nothing lost |
| Related work | 4 concessions ("we do not claim…") | comparative positioning: what the classical result is, what differs here |
| Encoding section | "A Lean-Checked Bridge to Diaconescu's Encoding" | "Localization inside the Many-Sorted Encoding"; credit stated plainly, added statement isolated |
| Formalization | §9 of the body | appendix, opening with an explicit statement that nothing above depends on it |

Two bibliography entries added (`BidoitHennicker2006`, `SannellaTarlecki2012`)
for the disambiguation.

Verified: no broken `\ref`/`\cref`, no broken `\cite`. No LaTeX toolchain
locally, so the build has not been run — that check is still outstanding.

## What was deliberately not done

No mathematics was changed, added, or removed. No theorem was restated, no
proof altered, no claim strengthened or weakened. Section 4's routine lemmas
were left in place: `EDITORIAL_GUARDRAILS.md` rule 7 ("reduce theorem count")
is right in general, but here the fact that the finite-base and old-fixing
criteria are *instances of one mechanism* is the actual contribution, and
cutting statements risks destroying the unification. Better to move routine
lemmas to an appendix than to delete them.

## What still needs a human

1. **Compile it.** No LaTeX here.
2. **The proofs themselves.** This pass made the mathematics visible; it did
   not check that each central proof is complete as prose. That is the core of
   the rebuild branch's job and it is the one thing that decides whether the
   next specialist reads past page 2.
3. **Do not resubmit to the same reviewer.** He declined, and said a report
   would be consultancy. Send the revision to a different reader in the same
   community.
