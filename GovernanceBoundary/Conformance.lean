import GovernanceBoundary.Spec.IdentifierMap

namespace GovernanceBoundary.Conformance

/-!
# Governance Boundary Conformance Predicate (v1)

This file provides a proof-carrying conformance interface for the
Governance Boundary (GB) layer using the stable requirement identifiers
defined in `GovernanceBoundary.Spec.IdentifierMap`.

Each identifier appears exactly once as:
- a ConformanceEvidence field
- an element in `requirements`

Ordering is alphabetical to remove editorial discretion.
-/

/-- Conjunction of a list of propositions. -/
def AndList : List Prop -> Prop
| [] => True
| p :: ps => p ∧ AndList ps

/-
GB conformance is treated as a structural predicate over evidence.
Interpretation semantics remain external.
-/
structure ConformanceEvidence where
  GB_ADAPTER_MANIFEST : Prop
  GB_CANONICAL_ENCODING : Prop
  GB_CONFORMANCE_SE_REQUIRED : Prop
  GB_DEFINITION_CORE : Prop
  GB_DEPENDENCY_GRAPH : Prop
  GB_FINGERPRINT : Prop
  GB_GOVERNANCE_ACTION : Prop
  GB_PROVENANCE : Prop
  GB_SCOPE_EXCLUSIONS : Prop
  GB_VERSIONING : Prop

/-- Alphabetized requirements list for GB v1. -/
def requirements (e : ConformanceEvidence) : List Prop :=
  [ e.GB_ADAPTER_MANIFEST
  , e.GB_CANONICAL_ENCODING
  , e.GB_CONFORMANCE_SE_REQUIRED
  , e.GB_DEFINITION_CORE
  , e.GB_DEPENDENCY_GRAPH
  , e.GB_FINGERPRINT
  , e.GB_GOVERNANCE_ACTION
  , e.GB_PROVENANCE
  , e.GB_SCOPE_EXCLUSIONS
  , e.GB_VERSIONING
  ]

/-- GB conformance predicate: all GB requirements hold. -/
def Conforms (e : ConformanceEvidence) : Prop :=
  AndList (requirements e)

/-- If `AndList ps` holds, then every member of `ps` holds. -/
theorem andList_of_mem {ps : List Prop} {p : Prop} :
    p ∈ ps -> AndList ps -> p := by
  intro hmem hand
  induction ps with
  | nil =>
      cases hmem
  | cons a tl ih =>
      have hand' : a ∧ AndList tl := by
        simpa [AndList] using hand
      have ha : a := hand'.1
      have hrest : AndList tl := hand'.2
      have hmem' : p = a ∨ p ∈ tl := by
        simpa using hmem
      cases hmem' with
      | inl hpa =>
          subst hpa
          exact ha
      | inr htail =>
          exact ih htail hrest

/-- Generic extractor: if `p` is listed and `Conforms` holds, then `p` holds. -/
theorem conforms_of_mem (e : ConformanceEvidence) (p : Prop) :
    p ∈ requirements e -> Conforms e -> p := by
  intro hmem hconf
  unfold Conforms at hconf
  exact andList_of_mem (ps := requirements e) (p := p) hmem hconf

end GovernanceBoundary.Conformance
