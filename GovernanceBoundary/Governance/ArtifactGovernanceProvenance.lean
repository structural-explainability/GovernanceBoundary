import Std
import GovernanceBoundary.Core.Base.Primitives

namespace GovernanceBoundary.Governance

/-!
REQ.GB.ARTIFACT.PROVENANCE:
  Structural provenance for governance actions on artifacts.

OBS:
  This is not general provenance (CEE covers interpretive provenance).
  This module records governance events such as approvals, publication,
  deprecation, and policy assignment as structure only.
-/

open GovernanceBoundary.Core.Base

/-- Governance action kind (structural; meaning external). -/
inductive GovernanceActionKind where
  | published
  | approved
  | deprecated
  | superseded
  | policyAssigned
  | policyRemoved
  deriving Repr, BEq, DecidableEq

/-- Target of a governance action. -/
structure GovernanceTarget where
  artifact : Uri
  version : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Structural record of a governance action. -/
structure GovernanceAction where
  actionId : VerifiableId
  kind : GovernanceActionKind
  target : GovernanceTarget
  actorId : Option VerifiableId := none
  occurredAt : DateTime
  rationaleRef : Option Uri := none
  deriving Repr, BEq, DecidableEq

/-- Minimal well-formedness (no semantics). -/
def GovernanceAction.WellFormed (a : GovernanceAction) : Prop :=
  a.actionId ≠ "" ∧ a.occurredAt ≠ "" ∧ a.target.artifact ≠ ""

end GovernanceBoundary.Governance
