import ResolutionOnePoint

namespace Resolution
namespace OnePoint

open Resolution.External

/-- The factorial-comb Cauchy sequence as a packaged representative. -/
noncomputable def factorialCauchySeq :
    Filtered.CauchySeq (generatedFilteredSpace alg) where
  term := factorialCombs
  cauchy := factorialCombs_cauchy

/-- The completion point represented by the factorial combs. -/
noncomputable def completionWitness :
    Filtered.Completion (generatedFilteredSpace alg) :=
  Filtered.classOf (generatedFilteredSpace alg) factorialCauchySeq

/-- The factorial-comb point is not the embedding of any generated Answer. -/
theorem completionWitness_ne_embed (x : Free.GeneratedAns alg) :
    completionWitness ≠ Filtered.embed (generatedFilteredSpace alg) x := by
  intro h
  apply noLimit x
  have hclass :
      Filtered.classOf (generatedFilteredSpace alg) factorialCauchySeq =
        Filtered.embed (generatedFilteredSpace alg) x := by
    simpa [completionWitness] using h
  have hconv :=
    (Filtered.classOf_eq_embed_iff
      (generatedFilteredSpace alg) factorialCauchySeq x).1 hclass
  simpa [factorialCauchySeq] using hconv

/-- The canonical embedding is not surjective for the one-point algebra. -/
theorem completionEmbedding_not_surjective :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace alg)) := by
  intro hsurj
  rcases hsurj completionWitness with ⟨x, hx⟩
  exact completionWitness_ne_embed x hx.symm

/-- The observational completion contains an explicit point outside the
    generated image. -/
theorem completion_adds_point :
    ∃ q : Filtered.Completion (generatedFilteredSpace alg),
      ∀ x : Free.GeneratedAns alg,
        Filtered.embed (generatedFilteredSpace alg) x ≠ q := by
  refine ⟨completionWitness, ?_⟩
  intro x
  exact Ne.symm (completionWitness_ne_embed x)

end OnePoint
end Resolution
