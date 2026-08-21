import ResolutionStrongTotalityV1Closure

/-!
# Strong Totality v1 axiom audit

This audit is intentionally separate from the manuscript-facing axiom audit.
It checks the final Strong Totality v1 interface, including the compact
free-pointed characterization and the constructive/classical boundary results.

The repository verification script permits only Lean's standard logical
quotient/extensionality dependencies (`propext`, `Classical.choice`, and
`Quot.sound`) and rejects any additional axiom dependency.
-/

#check Resolution.StrongTotality.resolution_freePointedCharacterization
#check Resolution.StrongTotality.strongTotality_v1_closed
#check Resolution.StrongTotality.strongTotality_v1_freePointed
#check Resolution.StrongTotality.strongTotality_v1_grand
#check Resolution.StrongTotality.strongTotality_v1_total
#check Resolution.StrongTotality.strongTotality_v1_exact
#check Resolution.StrongTotality.strongTotality_v1_wellFormedDomain
#check Resolution.StrongTotality.strongTotality_v1_proofCarryingBoundary
#check Resolution.StrongTotality.strongTotality_v1_noUniformCollapse

#print axioms Resolution.StrongTotality.resolution_freePointedCharacterization
#print axioms Resolution.StrongTotality.strongTotality_v1_closed
#print axioms Resolution.StrongTotality.strongTotality_v1_freePointed
#print axioms Resolution.StrongTotality.strongTotality_v1_grand
#print axioms Resolution.StrongTotality.strongTotality_v1_total
#print axioms Resolution.StrongTotality.strongTotality_v1_exact
#print axioms Resolution.StrongTotality.strongTotality_v1_wellFormedDomain
#print axioms Resolution.StrongTotality.strongTotality_v1_proofCarryingBoundary
#print axioms Resolution.StrongTotality.strongTotality_v1_noUniformCollapse
