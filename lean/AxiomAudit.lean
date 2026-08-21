import FiniteComplementTopology

/-!
# Axiom audit for the supplementary formal interface

The current manuscript is self-contained and does not attach Lean declaration
names to individual statements.  This audit therefore checks the small
publication-facing facade in `FiniteComplementTopology.lean`, rather than the
larger historical development tree.

Only Lean's standard logical infrastructure is permitted by
`scripts/check_axiom_audit.py`.
-/

#check FiniteComplementTopology.freeCompatibleExtensionUniversal
#check FiniteComplementTopology.finiteComplementSeparation
#check FiniteComplementTopology.baseClosedIffTotal
#check FiniteComplementTopology.pointwiseFixedContextGivesProperCompletion
#check FiniteComplementTopology.naturalNumbersExampleGivesProperCompletion
#check FiniteComplementTopology.prefixDepthCauchyNotFiniteComplementCauchy

#print axioms FiniteComplementTopology.freeCompatibleExtensionUniversal
#print axioms FiniteComplementTopology.finiteComplementSeparation
#print axioms FiniteComplementTopology.baseClosedIffTotal
#print axioms FiniteComplementTopology.pointwiseFixedContextGivesProperCompletion
#print axioms FiniteComplementTopology.naturalNumbersExampleGivesProperCompletion
#print axioms FiniteComplementTopology.prefixDepthCauchyNotFiniteComplementCauchy
