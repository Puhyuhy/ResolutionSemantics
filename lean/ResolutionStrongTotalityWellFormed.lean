import ResolutionStrongTotalityCanonicalObstruction

/-!
# Well-formed specification syntax

The foundational slogan of Strong Totality quantifies over *well-formed*
mathematical specifications.  The base `Specification` type is already semantic:
once a candidate type and acceptance predicate have been supplied, the object is
well-typed by construction.  This module separates that semantic layer from a
prior raw-presentation layer.

A specification language consists of raw codes together with a partial decoder.
A code is well-formed exactly when decoding succeeds.  Resolution semantics is
then defined only for a decoded specification.  The main theorem states the
intended domain condition exactly:

  a raw code has Resolution semantics iff it is well-formed.

Thus Strong Totality does not manufacture semantics for malformed syntax.  It
is total precisely on the domain of meaningful specifications.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- An abstract language of raw mathematical specifications.  The decoder is
partial because not every syntactic object need denote a meaningful typed
specification. -/
structure SpecificationLanguage where
  Code : Type v
  decode : Code -> Option Specification.{u}

namespace SpecificationLanguage

/-- A raw code is well-formed exactly when it decodes to some semantic
specification. -/
def WellFormed (L : SpecificationLanguage.{u,v}) (c : L.Code) : Prop :=
  Exists fun S : Specification.{u} => L.decode c = some S

/-- Package a well-formed raw code with the semantic specification it decodes
to. -/
structure Decoded (L : SpecificationLanguage.{u,v}) (c : L.Code) where
  specification : Specification.{u}
  decodes : L.decode c = some specification

/-- Every well-formed code has decoded semantic data. -/
theorem wellFormed_iff_nonempty_decoded
    (L : SpecificationLanguage.{u,v})
    (c : L.Code) :
    L.WellFormed c ↔ Nonempty (L.Decoded c) := by
  constructor
  · intro h
    rcases h with ⟨S, hS⟩
    exact ⟨⟨S, hS⟩⟩
  · intro h
    rcases h with ⟨d⟩
    exact ⟨d.specification, d.decodes⟩

/-- Resolution data attached to a raw code consists of a decoded semantic
specification together with a Resolution Answer for that specification.  The
universe is raised once because the decoded package itself contains a semantic
`Specification`, rather than merely a candidate value. -/
structure RawResolution
    (L : SpecificationLanguage.{u,v})
    (c : L.Code) : Type (max (u + 1) v) where
  decoded : L.Decoded c
  answer : ResolutionAnswer decoded.specification

/-- Every well-formed raw specification has Resolution semantics. -/
theorem wellFormed_has_resolution
    (L : SpecificationLanguage.{u,v})
    (c : L.Code)
    (h : L.WellFormed c) :
    Nonempty (L.RawResolution c) := by
  rcases h with ⟨S, hS⟩
  exact ⟨{
    decoded := ⟨S, hS⟩
    answer := ResolutionAnswer.residual
  }⟩

/-- Conversely, Resolution semantics for a raw code certifies that the raw code
was well-formed in the first place. -/
theorem resolution_implies_wellFormed
    (L : SpecificationLanguage.{u,v})
    (c : L.Code) :
    Nonempty (L.RawResolution c) -> L.WellFormed c := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.decoded.specification, r.decoded.decodes⟩

/-- **Well-formed Strong Totality.**  A raw mathematical specification has a
Resolution interpretation exactly when it is well-formed. -/
theorem rawResolution_nonempty_iff_wellFormed
    (L : SpecificationLanguage.{u,v})
    (c : L.Code) :
    Nonempty (L.RawResolution c) ↔ L.WellFormed c := by
  constructor
  · exact resolution_implies_wellFormed L c
  · exact wellFormed_has_resolution L c

/-- Uniform form of Strong Totality over an entire raw specification language:
all well-formed codes admit Resolution semantics. -/
theorem wellFormedStrongTotality
    (L : SpecificationLanguage.{u,v}) :
    forall c : L.Code,
      L.WellFormed c -> Nonempty (L.RawResolution c) := by
  intro c h
  exact wellFormed_has_resolution L c h

/-- Malformed syntax cannot accidentally acquire Resolution semantics. -/
theorem malformed_no_resolution
    (L : SpecificationLanguage.{u,v})
    (c : L.Code)
    (h : Not (L.WellFormed c)) :
    Not (Nonempty (L.RawResolution c)) := by
  intro hr
  exact h (resolution_implies_wellFormed L c hr)

/-- A total decoder recovers the original semantic setting as a special case:
every raw code is automatically well-formed. -/
def ofTotal
    (Code : Type v)
    (decode : Code -> Specification.{u}) : SpecificationLanguage.{u,v} where
  Code := Code
  decode := fun c => some (decode c)

/-- Codes in a language created from a total decoder are all well-formed. -/
theorem ofTotal_wellFormed
    (Code : Type v)
    (decode : Code -> Specification.{u})
    (c : Code) :
    (ofTotal Code decode).WellFormed c := by
  exact ⟨decode c, rfl⟩

end SpecificationLanguage

end StrongTotality
end Resolution
