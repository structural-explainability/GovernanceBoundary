namespace GovernanceBoundary.Governance

/-!
REQ.GB.FINGERPRINT:
  Structural fingerprint record shape for artifacts.

OBS:
  Fingerprints are identifiers, not truth claims.
  This module records digest material and algorithm identifiers structurally.
-/

abbrev Uri := String
abbrev Sha256 := String

/-- Hash algorithm identifier (structural). -/
inductive HashAlg where
  | sha256
  deriving Repr, BEq, DecidableEq

/-- Fingerprint over an artifact under an encoding profile. -/
structure Fingerprint where
  artifact : Uri
  alg : HashAlg := HashAlg.sha256
  digest : Sha256
  encodingProfile : Option Uri := none
  deriving Repr, BEq, DecidableEq

def Fingerprint.WellFormed (f : Fingerprint) : Prop :=
  f.artifact ≠ "" ∧ f.digest ≠ ""

end GovernanceBoundary.Governance
