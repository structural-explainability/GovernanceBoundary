namespace GovernanceBoundary.Core

structure ChangeControl where
  processRef : Option String := none
  approverRef : Option String := none
  deriving Repr, BEq, DecidableEq

def ScopeExclusions : Prop := True

end GovernanceBoundary.Core
