# Mapping: Paper to Lean Formalization

This document maps the conceptual structure of paper to its Lean formalization.

**Paper**: "Substrate Stability Under Persistent Disagreement:
Structural Constraints for Neutral Ontologies (Case, 2025)

**Formalization**: `StructuralExplainability/IdentityRegimes.lean`

The goal of this mapping is traceability, not redundancy:
every substantive claim in the paper corresponds either to
a Lean definition, an explicit axiom, or a proved theorem.

## Domain Scope

The formalization applies to ontological substrates optimized for:

- Stability under durable interpretive disagreement
- Accountability across legal, political, and analytic frameworks
- Neutrality, understood as exclusion of causal and normative execution
- Structural sufficiency

It does not apply to:

- Ontologies embedding causal or normative conclusions
- Systems relying on negotiated or consensus semantics
- Role-based or context-discriminated substrates
- Single-framework modeling environments

## High-Level Result

Paper Claim

> Exactly six identity-and-persistence regimes are **necessary and sufficient**
> for any accountability substrate optimized for stability under persistent
> disagreement.

Lean Result

The claim is realized as two theorems:

- A necessity theorem - any satisfying substrate must have at least six regimes
- A sufficiency theorem - there exists a substrate with exactly six regimes
  satisfying all requirements

These are bundled in:

```lean
theorem six_regimes_theorem :
  (∀ (satisfies : Regime -> Requirement -> Prop)
     (S : Substrate Regime),
     S.satisfiesAll satisfies -> S.card >= 6)
  ∧
  (∃ S : Substrate CanonicalRegime,
     S.card = 6 ∧ S.satisfiesAll canonicalSatisfies)
```

---

## Structural Requirements (R1–R6)

Paper Concepts

The paper identifies six regime-forcing structural requirements:

| ID  | Requirement (informal)                          |
| --- | ----------------------------------------------- |
| R1  | Obligation-bearing capacity (Actor / non-Actor) |
| R2  | Acted-upon / locus capacity                     |
| R3  | Authority-grounding capacity                    |
| R4  | Time-indexed occurrence                         |
| R5  | Applicability / scope                           |
| R6  | Descriptive record / observation                |

These requirements are independent and structural.
They do not name concrete kinds, roles, or domains.

Lean Representation

```lean
inductive Requirement where
  | R1 | R2 | R3 | R4 | R5 | R6
  deriving DecidableEq, Repr, Fintype
```

A cardinality lemma confirms the enumeration:

```lean
theorem requirement_count : Fintype.card Requirement = 6
```

## Regimes and Substrates

Paper Concepts

- A regime specifies identity and persistence conditions.
- A substrate consists of a finite set of regimes.
- Regimes are not named or instantiated at this level.

Lean Representation

```lean
variable {Regime : Type} [DecidableEq Regime]
abbrev Substrate (Regime : Type) [DecidableEq Regime] := Finset Regime
```

This ensures the proof does not smuggle in six via enumeration.

## Satisfaction Relation

Paper Concepts

A regime _satisfies_ a requirement if it can discharge that structural role
without appeal to hidden discriminators (roles, norms, causation, etc.).

Lean Representation

The satisfaction relation is left abstract:

```lean
satisfies : Regime -> Requirement -> Prop
```

A substrate satisfies a requirement if it contains some satisfying regime:

```lean
def Substrate.satisfiesReq :
  (Regime -> Requirement -> Prop) ->
  Substrate Regime -> Requirement -> Prop
```

A substrate satisfies all requirements if it satisfies each R1–R6:

```lean
def Substrate.satisfiesAll :
  (Regime -> Requirement -> Prop) ->
  Substrate Regime -> Prop
```

---

## Axiom: Independence / Non-Collapse

Paper Claim

The six requirements are independent:
no single regime can satisfy two distinct requirements
without introducing hidden discriminators.

This is the core structural assumption behind the lower bound.

Lean Axiom

```lean
axiom satisfies_functional
  (satisfies : Regime -> Requirement -> Prop)
  (r : Regime) (req1 req2 : Requirement) :
  satisfies r req1 -> satisfies r req2 -> req1 = req2
```

Role in the Proof

- This axiom is the only source of the ≥ 6 necessity bound.
- Removing or weakening it invalidates the necessity theorem.
- The axiom is explicitly documented with an `OBS` block in the Lean file.

## Necessity Theorem

Paper Argument

1. Each requirement must be satisfied by some regime.
2. Independence forces these regimes to be distinct.
3. Therefore, at least six regimes are required.

Lean Theorem

```lean
theorem six_regimes_necessary :
  ∀ (satisfies : Regime -> Requirement -> Prop)
    (S : Substrate Regime),
    S.satisfiesAll satisfies -> S.card >= 6
```

## Sufficiency Theorem

Paper Argument

There exists a substrate with exactly six regimes that satisfies all requirements.

Lean Construction (Canonical Model)

- Regimes are identified with requirements:
  ```lean
  abbrev CanonicalRegime := Requirement
  ```
- Satisfaction is equality:
  ```lean
  def canonicalSatisfies r req := r = req
  ```
- Substrate is the full set:
  ```lean
  def canonicalSubstrate := Finset.univ
  ```

Lean Theorem

```lean
theorem six_regimes_sufficient :
  ∃ S : Substrate CanonicalRegime,
    S.card = 6 ∧ S.satisfiesAll canonicalSatisfies
```

## What the Formalization Does Not Do

- It does not name concrete kinds (Actor, Event, etc.)
- It does not embed causal or normative semantics
- It does not assume any domain-specific ontology
- It does not prove that only one six-regime realization exists

## Summary

| Aspect                | Status                   |
| --------------------- | ------------------------ |
| Six requirements      | Explicit (`Requirement`) |
| Independence          | Explicit axiom           |
| Necessity (≥ 6)       | Proven                   |
| Sufficiency (6 exist) | Proven                   |
| Concrete kinds        | Intentionally absent     |
| Proof completeness    | No `sorry`               |
| Domain assumptions    | Explicit and documented  |

This mapping ensures that the paper's claims and
the Lean formalization remain aligned, auditable,
and stable under revision.
