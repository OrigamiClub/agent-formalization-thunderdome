# agent_082 — Improved sunflower lemma (statement only)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type) [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ core T, T ⊆ W ∧ r ≤ T.card ∧ IsSunflower core T
```

with a local `def IsSunflower (core : Finset α) (petals : Finset (Finset α)) : Prop`
defined as `(petals : Set (Finset α)).Pairwise fun S T => S ∩ T = core`.

## Encoding decisions and why

- **Set representation.** Sets are `Finset α` over an ambient type `α`; the family is
  `W : Finset (Finset α)`. This makes "finite family" and all three cardinalities
  (`W.card`, `S.card`, `T.card`) plain `Finset.card`, and membership distinctness of
  the family is automatic.
- **`α : Type` quantified *inside* the `∃ C`.** This makes `C` a genuinely absolute
  constant — it cannot depend on the ambient type. WLOG restricting to `Type` (universe
  0) is harmless: the lemma only concerns finite families of finite sets. `[DecidableEq
  α]` is needed for `Finset` intersection.
- **Sunflower predicate.** Defined explicitly via `Set.Pairwise` on the coerced family:
  "any two distinct members meet in exactly `core`". With `r ≥ 2` members this forces
  `core` to be the common intersection, gives `core ⊆ S` for each member, and makes the
  petals `S \ core` pairwise disjoint — so those need not be stated separately. Petals
  are *not* required nonempty (a sunflower can have empty petals, i.e. include the core
  itself once). Distinctness of the `r` members is handled by `Set.Pairwise` (only
  distinct pairs constrained) together with `T` being a `Finset` (no repeats).
- **`r ≤ T.card` rather than `T.card = r`.** Mirrors Mathlib's classical
  `sunflower_exists`-style conclusion; any `r`-subfamily of a larger sunflower is still
  a sunflower, so the two are interchangeable. "with `r` petals" is read as "at least
  `r`".
- **Logarithm.** `Real.log` (natural log). The RHS is real, so the size hypothesis is
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` with `k : ℕ` in the exponent (monoid
  power). Any other base only rescales `C`, which is existentially quantified, so the
  choice is immaterial to the statement's content.
- **Small `k`.** Guarded by `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes the bound `0`
  and the statement false (r distinct singletons need `|W| ≥ r`, not `> 0`); for
  `k = 0` it is degenerate. Restricting to `k ≥ 2` matches the usual informal
  convention "assume `k ≥ 2`". `r` is kept at `1 ≤ r` per "positive integers".
- **`C` existential, inside the theorem**, rather than a named `noncomputable def` or a
  hypothesis, so the file states exactly "there exists an absolute constant".

## Uncertainties / guessed identifiers

- Mathlib does have a sunflower file `Mathlib.Combinatorics.SetFamily.Sunflower` with a
  predicate `Finset.IsSunflower` and the *classical* Erdős–Rado bound. I did not rely
  on its exact name or argument order; I defined a local `IsSunflower` instead. If the
  Mathlib predicate is `IsSunflower (𝒮) (core)` (family first), swapping to it is
  purely cosmetic.
- The *improved* bound is (to my knowledge) not in Mathlib, so nothing here reuses a
  library statement.
- `import Mathlib` is used for robustness (pulls in `Real.log`, `Finset`, `Set.Pairwise`).
  Minimal imports would be `Mathlib.Analysis.SpecialFunctions.Log.Basic` and
  `Mathlib.Combinatorics.SetFamily.Sunflower`.
- The `∀ (α : Type) [DecidableEq α]` binder after an existential is valid Lean 4 syntax;
  if a checker dislikes the instance binder there, replace with
  `∀ (α : Type), [DecidableEq α] → ...` / make `α` a section variable (at the cost of
  letting `C` depend on `α`).
