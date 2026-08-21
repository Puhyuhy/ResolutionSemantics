import ResolutionSemantics
import ResolutionIntrinsicFiniteComplementAPI
import ResolutionResidualComparisonPublic
import ResolutionOldFixingContextPropernessPublic
import ResolutionCompletionProbe

/-!
# Finite-complement topology: supplementary formal interface

This module is the publication-facing entry point for the Lean development
accompanying *A Finite-Complement Congruence Topology for Partial Algebras*.

The manuscript is self-contained and its current theorem statements are not
claimed to have a one-to-one formalization.  The declarations below expose the
parts of the development that directly support the paper:

* the universal property of the free compatible total extension;
* qualitative separation by compatible extensions with finite complement;
* the criterion saying that the embedded base is closed exactly in the total
  case;
* the pointwise-fixed-context special case of the paper's incompleteness
  criterion, including the natural-number example;
* the explicit distinction between prefix-depth Cauchy behaviour and the
  finite-complement observation uniformity.

The generalized uniformly-finite-orbit criterion and the nowhere-defined
discrete example in the manuscript are proved there directly and are not
presented here as separately formalized theorems.

Some imported modules retain historical identifiers such as `old`, `finiteTag`,
and `ResolutionSemantics`.  They are implementation names from earlier stages
of the project.  This facade uses the current paper's terminology wherever a
new public name is introduced.
-/

universe u v w

namespace FiniteComplementTopology

variable {Sigma : Resolution.Signature.{u}}

/-- A partial algebra in the binary-signature formalization used by the
manuscript. -/
abbrev PartialAlgebra := Resolution.PartialAlg

/-- The generated carrier of the free compatible total extension. -/
abbrev FreeCompatibleExtension
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  ResolutionSemantics.Generated D

/-- A compatible total target for the free universal property. -/
abbrev CompatibleTotalAlgebra
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.Free.CompatibleAlg D

/-- The free compatible total extension has the expected universal property. -/
theorem freeCompatibleExtensionUniversal
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.CompatibleAlg.{u,v,w} D) :
    ∃ F : Resolution.Free.CompatibleHom D T,
      ∀ G : Resolution.Free.CompatibleHom D T, G = F :=
  ResolutionSemantics.freeCompletionUniversal D T

/-- Every pair of distinct generated elements can be separated by a compatible
extension whose complement over the embedded base is finite. -/
theorem finiteComplementSeparation
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.External.IntrinsicFiniteComplementSeparating D :=
  ResolutionSemantics.qualitativeFiniteComplementSeparating_theorem D

/-- The embedded base is closed under every generated total operation exactly
when the original partial algebra was already total. -/
theorem baseClosedIffTotal
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    ResolutionSemantics.ResidualComparison.GeneratedOldClosed D ↔
      Resolution.FiniteBaseProperness.IsTotal D :=
  ResolutionSemantics.ResidualComparison.generatedOldClosedIffEvaluatorTotal D

/-- A context that fixes every base element pointwise and starts from an
undefined base application yields a non-surjective completion embedding.

This is the pointwise-fixed special case of the more general
uniformly-finite-base-orbit criterion proved in the manuscript. -/
theorem pointwiseFixedContextGivesProperCompletion
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : ResolutionSemantics.OldFixingContextCompletion.Witness D) :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D)) :=
  ResolutionSemantics.OldFixingContextCompletion.embeddingNotSurjective D W

/-- The natural-number example with the undefined seed `0 / 0` and the context
`x ↦ x + 0` satisfies the pointwise-fixed special case. -/
theorem naturalNumbersExampleGivesProperCompletion :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace
          Resolution.External.NatArithmetic.alg)) :=
  ResolutionSemantics.NatDivision.oldFixingCriterion

/-- Prefix-depth Cauchy behaviour and finite-complement observational Cauchy
behaviour differ whenever one base application is undefined.

Internally, `generatedFilteredSpace` uses the historical finite-tag
presentation.  Its stage parameter counts explicit tags while retaining one
additional overflow state; therefore the one-tag witness used in the imported
probe corresponds to two points outside the base in the manuscript's current
complement-size convention. -/
theorem prefixDepthCauchyNotFiniteComplementCauchy
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    (h : D.eval f a z = none) :
    ∃ s : Nat -> Resolution.Free.GeneratedAns D,
      Resolution.Filtered.Cauchy (Resolution.Probe.depthSpace D) s ∧
      ¬ Resolution.Filtered.Cauchy
        (Resolution.External.generatedFilteredSpace D) s :=
  Resolution.Probe.depthCauchy_not_observationalCauchy D f a z h

end FiniteComplementTopology
