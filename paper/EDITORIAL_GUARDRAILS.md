# Paper I — Editorial Guardrails After Specialist Feedback

This file records the writing constraints for the rebuild branch.

## Why a rebuild is required

External specialist feedback on the historical manuscript identified a serious presentation problem: the paper was not written to ordinary mathematical-paper conventions and was difficult to read as mathematics.

The response is **not** cosmetic editing. The paper must be rebuilt from mathematical statements and proofs.

## Non-negotiable rules

### 1. The paper must be self-contained

A reader must be able to understand every definition, theorem, and central proof without consulting GitHub, Lean source, generated theorem maps, or CI logs.

### 2. Standard mathematics first

When literature already has accepted terminology, notation, and categorical/algebraic framing, use it. Introduce project terminology only where it denotes genuinely additional structure.

### 3. Proofs are prose mathematics

For every central theorem:

- state the hypotheses in ordinary notation;
- explain the construction;
- identify the invariant or key lemma;
- prove the conclusion step by step;
- only afterward mention the corresponding Lean declaration.

### 4. Do not advertise formalization as mathematical novelty

Lean verification establishes machine-checked correctness of the formal statements. It does not establish historical priority or mathematical significance.

### 5. Separate established machinery from candidate contributions

The manuscript should make it visually and logically obvious which ingredients are classical/background and which exact statements are being proposed as the paper's contribution.

### 6. Avoid internal-development language

Do not expose historical phase numbers, CI implementation details, branch names, or source-level helper names in the mathematical narrative.

### 7. Reduce theorem count

A shorter paper with one strong theorem is preferable to a long catalogue of correct but routine lemmas.

### 8. Related work is comparative, not defensive

For each closest area, say precisely:

- what the established result is;
- what hypotheses/objects it uses;
- what our theorem changes;
- whether the relation is exact, special-case, stronger/weaker, or only analogous.

### 9. Limitations must be explicit

Do not imply that the construction assigns conventional numeric values to undefined arithmetic, proves unsatisfiability from residuality, or supersedes established totalization frameworks.

### 10. Formalization section stays small

The final paper may include a concise verification section and theorem map, but the formalization must remain supplemental to the human mathematical argument.

## Manuscript skim test

Before release, a specialist reading only:

- title;
- abstract;
- introduction;
- definitions;
- theorem statements;
- proof openings;
- related work;
- conclusion

should be able to answer all of the following:

1. What mathematical object is being studied?
2. What is already known?
3. What exact theorem is claimed here?
4. Why is its hypothesis class unusual or useful?
5. What is the proof idea?
6. What does the theorem **not** say?

If any answer requires opening Lean, the rebuild has failed.
