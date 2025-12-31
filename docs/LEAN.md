# Lean 4 Quick Reference (Six Regimes Proof)

This document lists **only the Lean constructs actually used**
in the abstract formalization of the *Six Regimes Theorem*.

It is intended as a local aid for readers of
`StructuralExplainability/IdentityRegimes.lean`,
not as a general Lean tutorial.

---

## Tactics Used

| Tactic | Meaning |
|--------|---------|
| `intro` | Introduce universally quantified variables or assumptions. |
| `have`  | Introduce an intermediate lemma or fact. |
| `exact`       | Provide a term that exactly satisfies the goal. |
| `simp`        | Simplify using definitions and rewriting rules. |
| `constructor` | Build a conjunction (`∧`) or existential (`∃`). |
| `refine`      | Provide a proof skeleton with placeholders. |
| `native_decide` | Compute decidable propositions (used for finite cardinalities). |

No automation-heavy tactics (`aesop`, `linarith`, etc.) are used.

---

## Logical Symbols

| Symbol | Meaning |
|-------:|---------|
| `∀`    | Universal quantification |
| `∃`    | Existential quantification |
| `→`    | Implication / function arrow |
| `∧`    | Logical conjunction |
| `=`    | Equality |
| `≠`    | Inequality |
| `≥`    | Greater-than-or-equal (on naturals) |
| `∈`    | Membership in a `Finset` |
| `⟨a, b⟩` | Pair / existential witness |

---

## Core Lean Keywords

| Keyword     | Role in this proof |
|-------------|--------------------|
| `inductive` | Define the six requirements (`Requirement`). |
| `axiom`     | Declare the non-collapse (independence) assumption. |
| `def`       | Define satisfaction and substrate predicates. |
| `theorem`   | State and prove necessity and sufficiency results. |
| `abbrev`    | Lightweight type aliases (`Substrate`, `CanonicalRegime`). |
| `variable`  | Declare abstract types (`Regime`) and relations. |
| `namespace` | Group all definitions under `StructuralExplainability`. |
| `deriving`  | Auto-generate `DecidableEq`, `Fintype`, etc. |

---

## Types and Structures Used

| Type   | Meaning |
|--------|---------|
| `Prop` | Logical propositions |
| `Type` | Types of regimes |
| `Finset α`   | Finite set of elements of type `α` |
| `{x // p x}` | Subtype (used for cardinality arguments) |

---

## Mathlib Concepts Used

| Concept        | Purpose |
|----------------|---------|
| `Fintype`      | Finite types (used for requirement count = 6). |
| `Fintype.card` | Cardinality of a finite type. |
| `Finset.card`  | Cardinality of a finite set. |
| `Finset.univ`  | Full finite set of a finite type. |
| `Function.Injective` | Used to prove lower cardinality bounds. |

---

## Proof-Level Constructions

| Construct     | Use |
|---------------|-----|
| `Classical.choose` | Select a witness from an existential hypothesis. |
| `Subtype.val` | Project value from `{x // p x}`. |
| `Fintype.card_le_of_injective` | Derive cardinality lower bound from injectivity. |

---

## Comment Syntax

| Syntax       | Purpose |
|--------------|---------|
| `--`         | Line comment |
| `/-- ... -/` | Doc comment (attached to a declaration) |
| `/-! ... -/` | Section or module documentation |
| `## OBS:`    | Structured observation / domain assumption (project convention) |

---

## Build Commands

| Command | Purpose |
|---------|---------|
| `lake clean` | Remove build artifacts. |
| `lake build` | Compile the project. |
| `lake exe verify` | Run verification executable. |

---

## What Is *Not* Used

The following are intentionally absent from this proof:

- Induction
- Pattern matching on data
- Lists or recursion
- Causal or normative primitives
- Automation tactics (`aesop`, `simp_all`, etc.)

The proof is **structural, cardinality-based, and axiom-delimited**.

---

## Reading Tip

If you can follow:
- injective functions ⇒ cardinality lower bounds, and
- existential witnesses ⇒ finite distinct elements,

then you can read the entire proof.
