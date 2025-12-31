namespace GovernanceBoundary.Spec

/-!
# Governance Boundary Identifiers (GB) -- Identifier Map (v1)

This file provides stable requirement identifiers for the Governance Boundary (GB)
specification as Lean constants.

These identifiers are the sole normative reference mechanism.
They are intended to align 1:1 with GB SPEC.md / CONFORMANCE.md identifiers.

OBS:
- Each identifier is defined exactly once in this file.
- Identifiers are listed in strict alphabetical order.
- Identifiers are represented as Strings so they can be reused across tooling.
- This file does not define semantics.
- This file must remain stable across minor revisions.
-/

-- Canonical identifier strings (alphabetical)

def GB_ADAPTER_MANIFEST : String := "GB.ADAPTER.MANIFEST"
def GB_CANONICAL_ENCODING : String := "GB.CANONICAL.ENCODING"
def GB_CONFORMANCE_SE_REQUIRED : String := "GB.CONFORMANCE.SE.REQUIRED"
def GB_DEFINITION_CORE : String := "GB.DEFINITION.CORE"
def GB_DEPENDENCY_GRAPH : String := "GB.DEPENDENCY.GRAPH"
def GB_FINGERPRINT : String := "GB.FINGERPRINT"
def GB_GOVERNANCE_ACTION : String := "GB.GOVERNANCE.ACTION"
def GB_PROVENANCE : String := "GB.PROVENANCE"
def GB_SCOPE_EXCLUSIONS : String := "GB.SCOPE.EXCLUSIONS"
def GB_VERSIONING : String := "GB.VERSIONING"

-- Optional: a canonical list for tooling / checks.
def all : List String :=
  [ GB_ADAPTER_MANIFEST
  , GB_CANONICAL_ENCODING
  , GB_CONFORMANCE_SE_REQUIRED
  , GB_DEFINITION_CORE
  , GB_DEPENDENCY_GRAPH
  , GB_FINGERPRINT
  , GB_GOVERNANCE_ACTION
  , GB_PROVENANCE
  , GB_SCOPE_EXCLUSIONS
  , GB_VERSIONING
  ]

end GovernanceBoundary.Spec
