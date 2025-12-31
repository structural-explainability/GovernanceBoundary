import Std
import GovernanceBoundary.Core.Base.Primitives

namespace GovernanceBoundary.Governance

/-!
REQ.GB.ADAPTER.MANIFEST:
  Structural declaration of adapter identity, scope, and claimed compatibility.

OBS:
  This is not an endorsement mechanism.
  It records what an adapter claims, in a structurally checkable shape.
-/

open GovernanceBoundary.Core.Base

/-- Minimal semantic version triple. -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Repr, BEq, DecidableEq

/-- Declares a dependency on a named artifact/version anchor. -/
structure DependencyDecl where
  artifact : Uri
  version : SemVer
  required : Bool := true
  deriving Repr, BEq, DecidableEq

/-- Adapter surface claim: input/output artifact classes it can handle. -/
structure AdapterSurface where
  consumes : List Uri := []
  produces : List Uri := []
  deriving Repr, BEq, DecidableEq

/-- Structural adapter manifest (claims only). -/
structure AdapterManifest where
  adapterId : VerifiableId
  adapterName : String
  adapterVersion : SemVer
  appliesTo : AdapterSurface
  dependsOn : List DependencyDecl := []
  notes : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Structural well-formedness predicate (intentionally small). -/
def AdapterManifest.WellFormed (m : AdapterManifest) : Prop :=
  m.adapterName ≠ "" ∧
  (m.appliesTo.consumes ≠ [] ∨ m.appliesTo.produces ≠ [])

end GovernanceBoundary.Governance
