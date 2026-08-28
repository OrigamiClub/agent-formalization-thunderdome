# agent_037 — improved sunflower lemma (statement only)

## Form chosen

A single existential-constant statement:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
  2 ≤ k → 0 < r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) → ContainsSunflower W r
```

with two auxiliary definitions: `IsSunflower P Y` (core-based) and
`ContainsSunflower W r`.

## Encoding decisions and why

- **Set representation:** `Finset (Finset α)` over an arbitrary type `α` with
  `[DecidableEq α]`. Everything in the statement is finite, so `Finset` keeps it
  computable and avoids carrying separate finiteness hypotheses. `α` is
  universe-polymorphic (`Type*`).
- **Sunflower definition:** explicit core. `IsSunflower P Y` says any two distinct
  members of `P` meet exactly in `Y`. This is the definition given in the task.
  I did not assume a Mathlib predicate exists (see uncertainties).
- **Petals / distinctness:** the petal family is a `Finset`, so distinctness of the
  `r` members is automatic; `P.card = r` is the "`r` distinct petals" condition.
  `P ⊆ W` encodes "contained in `W`".
- **Petal nonemptiness:** not stated. For `r ≥ 2` and equal cardinalities `k ≥ 1`
  the core is a strict subset of each member, so petals are automatically
  nonempty; a separate hypothesis would be redundant.
- **Constant `C`:** existentially quantified, and quantified *before* `α, k, r`, so
  it is a single absolute constant uniform over all ambient types and all `k, r`.
  Chose existential (rather than a hypothesis or a named opaque constant) so the
  file is self-contained and the statement carries its full content.
- **Logarithm:** `Real.log` (natural log), argument `(k : ℝ)`. Base choice only
  rescales `C`, so natural log is the least-friction Mathlib choice.
- **`k = 0, 1` edge cases:** handled by requiring `2 ≤ k`. At `k = 1`,
  `Real.log 1 = 0` makes the RHS `0` and the implication "`|W| > 0 →` sunflower"
  is false (e.g. `r` cannot be found), so `k = 1` is genuinely outside the clean
  statement. `k = 0` (all sets empty) is likewise excluded. Alternative renderings
  (`Real.log (k+1)`, `max (Real.log k) 1`) would also work and only change `C`;
  `2 ≤ k` was chosen as the most transparent.
- **`r`:** `0 < r`. `r = 1` is harmless (any nonempty family trivially has a
  1-petal "sunflower"); `r = 0` is excluded to keep `P.card = r` meaningful.
- **Cardinality:** `Finset.card` throughout, compared in `ℝ` via coercion, with
  strict `<` matching "`|W| >` bound".

## Uncertainties

- **Possible Mathlib name collision / existing API.** Mathlib may already contain a
  sunflower predicate (something like `IsSunflower` / `Finset.IsSunflower` and an
  Erdős–Rado `exists_sunflower` lemma). I was not confident of its exact name or
  argument order, so I defined my own inside `namespace ImprovedSunflower` to avoid
  any clash under `import Mathlib`. If the Mathlib predicate exists, my
  `IsSunflower` should be defeq/equivalent to it (core-based, two distinct members
  meet in the core).
- **`Real.log` identifier** is standard Mathlib; assumed correct. `import Mathlib`
  is used to sidestep import-path guessing.
- Placing `{α : Type*} [DecidableEq α]` binders inside the `∀` under `∃ C` is
  valid Lean 4; assumed no elaboration issue (no compiler was available to check).
