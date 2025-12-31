namespace GovernanceBoundary.Core

structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Repr, BEq, DecidableEq

def VersionedOnly : Prop := True

end GovernanceBoundary.Core
