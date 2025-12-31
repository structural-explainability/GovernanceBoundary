namespace GovernanceBoundary.Governance

/-!
REQ.GB.CANONICAL.ENCODING:
  Structural requirements for canonical encodings and hashing.

OBS:
  This module does not prescribe a single canonicalization algorithm.
  It provides a record shape to declare canonical encoding requirements
  and to bind a hash to an encoding profile identifier.
-/

abbrev Uri := String
abbrev Sha256 := String

/-- Declares an encoding profile by identifier only (semantics external). -/
structure EncodingProfile where
  profileUri : Uri
  profileVersion : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Declares a canonicalization requirement by reference to a profile. -/
structure CanonicalEncodingReq where
  appliesTo : Uri
  profile : EncodingProfile
  requiresDeterminism : Bool := true
  requiresStableOrdering : Bool := true
  deriving Repr, BEq, DecidableEq

/-- Binds a hash to an artifact under a declared encoding profile. -/
structure CanonicalHashBinding where
  artifact : Uri
  profile : EncodingProfile
  digest : Sha256
  deriving Repr, BEq, DecidableEq

def CanonicalHashBinding.WellFormed (b : CanonicalHashBinding) : Prop :=
  b.artifact ≠ "" ∧ b.profile.profileUri ≠ "" ∧ b.digest ≠ ""

end GovernanceBoundary.Governance
