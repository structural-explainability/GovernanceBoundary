import Std

namespace GovernanceBoundary.Governance

/-!
REQ.GB.DEPENDENCY.GRAPH:
  Structural dependency graph for governance-level artifacts.

OBS:
  This is not the EP evolution graph.
  It is a governance graph describing dependencies among artifacts
  (specs, adapters, profiles, appendices) by identifier only.
-/

abbrev Uri := String

/-- Directed dependency edge: `from` depends on `to`. -/
structure DepEdge where
  «from» : Uri
  «to» : Uri
  required : Bool := true
  deriving Repr, BEq, DecidableEq

/-- Dependency graph as an edge list (structural). -/
structure DependencyGraph where
  edges : List DepEdge := []
  deriving Repr, BEq, DecidableEq

def DepEdge.WellFormed (e : DepEdge) : Prop :=
  e.«from» ≠ "" ∧ e.«to» ≠ "" ∧ e.«from» ≠ e.«to»

def DependencyGraph.WellFormed (g : DependencyGraph) : Prop :=
  ∀ e ∈ g.edges, DepEdge.WellFormed e

end GovernanceBoundary.Governance
