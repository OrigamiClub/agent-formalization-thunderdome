# agent_026 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮
```

plus an auxiliary `def IsSunflower`.

## Encoding decisions and rationale

- **Set representation.** `Finset α` over an ambient type `α : Type u`, with the
  family `W : Finset (Finset α)`. Finiteness of the family and of each member is
  then automatic, cardinalities are `Finset.card`, and distinctness of the
  members of any subfamily `𝒮 : Finset (Finset α)` is automatic. `[DecidableEq α]`
  is needed for `∩` on `Finset`.

- **Sunflower predicate.** Defined explicitly with an explicit core `Y`:
  `𝒮.card = r` (so exactly `r` distinct sets), `∀ S ∈ 𝒮, Y ⊆ S`, and
  `∀ S₁ S₂ ∈ 𝒮, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`. The last clause is the standard
  "all pairwise intersections coincide" condition; it already implies `Y ⊆ S`
  whenever `r ≥ 2`, but the explicit `Y ⊆ S` clause keeps the definition sensible
  for `r ≤ 1` and matches the informal "core" wording. Pairwise-disjoint petals
  `S \ Y` and the "in ≥ 2 sets ⇒ in all" property are consequences, not
  hypotheses. Petals are allowed to be empty (at most one member can equal `Y`).

- **"Contains a sunflower".** `∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮`. The core `Y` is
  existentially quantified; `𝒮 ⊆ W` says the sunflower is drawn from the family.

- **Logarithm.** `Real.log` (natural log), applied to `(k : ℝ)`. The lemma is
  base-independent: switching to `Real.logb 2` or `Real.logb` any fixed base
  rescales `log` by a constant, absorbed into `C`. `Nat.log 2` would also work up
  to the constant but introduces floor noise, so I avoided it.

- **Handling small `k`.** Hypothesis `2 ≤ k`. For `k = 0`, `Real.log 0 = 0`
  (Mathlib junk value) and the bound is meaningless; for `k = 1`,
  `Real.log 1 = 0` makes the right-hand side `0`, and `|W| > 0` cannot force `r`
  distinct sets. Restricting to `k ≥ 2` is the usual domain for this statement.
  Alternative faithful formulation valid for all `k ≥ 1`: keep `1 ≤ k` and use
  `(C * r * (Real.log k + 1)) ^ k` as the threshold; the `+1` is absorbed by `C`
  for large `k` and rescues `k = 1`. I chose the cleaner `k ≥ 2` version.

- **`r`.** Hypothesis `1 ≤ r`. The statement is only interesting for `r ≥ 2` (or
  the classical `r ≥ 3`), but "for all positive integers `r`" is honoured and the
  `r = 1` case is trivially true.

- **Constant `C`.** Existentially quantified, and crucially placed *outside* the
  quantifiers over `α, k, r, W`, so it is a single absolute constant. Bundled
  with `0 < C`.

- **Strictness.** The literature's `|W| > (C r log k)^k` is rendered as the strict
  `(...)^k < (W.card : ℝ)`.

- **Universe.** `universe u` with `α : Type u` so the theorem is universe
  polymorphic while `C` stays absolute.

## Uncertainties

- I do **not** rely on any Mathlib sunflower API. I believe Mathlib as of early
  2026 has no improved sunflower lemma, and I am not certain whether it has a
  `Sunflower` / `IsSunflower` predicate at all (possible names would be something
  like `Finset.IsSunflower` or `Set.IsSunflower` under
  `Mathlib/Combinatorics/SetFamily/`). To be safe I define `IsSunflower` locally.
  If a Mathlib predicate exists it may differ in details (indexed family vs
  `Finset (Finset α)`, whether the core is explicit, whether petals must be
  nonempty).

- `Real.log`, `Real.logb` identifiers are standard and I am confident in them.

- Elaboration detail: a `∀ {α : Type u} [DecidableEq α] ...` binder appearing to
  the right of `∃ C, 0 < C ∧ ...` inside a theorem statement is expected to be
  fine in Lean 4 / Mathlib, but I could not machine-check it (no compiler). If it
  were rejected, the fix is to curry the constant out as
  `∃ C : ℝ, 0 < C ∧ ∀ ...` still works, or to state it as two declarations
  (a `def sunflowerConst` / hypothesis form).
