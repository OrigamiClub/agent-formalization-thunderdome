# agent_055 — improved sunflower lemma (statement only)

## Form chosen

One theorem, `improved_sunflower_lemma`, of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * max 1 (Real.log k)) ^ k < (W.card : ℝ) →
    ∃ 𝒮 ⊆ W, IsSunflowerWithPetals r 𝒮
```

plus two auxiliary definitions, `IsSunflower` (core version) and
`IsSunflowerWithPetals` (adds the petal count).

## Encoding decisions and why

- **Set representation.** `Finset α` over an ambient `[DecidableEq α]` type; the
  family is `W : Finset (Finset α)`. This makes "distinct sets" automatic (a
  `Finset` has no duplicates), avoids carrying finiteness hypotheses, and gives
  `Finset.card` directly for the "cardinality exactly `k`" condition.

- **Sunflower predicate.** Defined explicitly via an explicit core:
  `IsSunflower Y 𝒮 := ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y`. This is the literal
  content of the definition in the task statement. The parenthetical consequences
  (pairwise-disjoint petals; any point in two members is in all) are theorems, not
  part of the definition, so they are omitted.

- **Petals nonempty?** Not required. The task's definition does not demand it, and
  `S ∩ T = Y` already forces `Y ⊆ S` for every member once `r ≥ 2`. At most one
  member can equal the core. Requiring `Y ⊂ S` was considered a distortion of the
  quoted definition, so it was left out.

- **`r` petals.** Encoded as `𝒮.card = r` (exact count). Since a subfamily of a
  sunflower is again a sunflower, `= r` and `≥ r` give equivalent theorems here.

- **The constant `C`.** Existentially quantified *inside* the statement, but placed
  *outside* the `∀ {α}` binder so that a single `C` works for every ambient type —
  i.e. it is genuinely absolute. Only `0 < C` is imposed (no need to fix a value).

- **Logarithm.** `Real.log` (natural log). The lemma's `log` is base-independent up
  to the constant `C`, so the base is immaterial; natural log is the Mathlib
  default and keeps the statement clean. The comparison is done in `ℝ`, coercing
  `W.card`, `k`, `r`.

- **Small `k`.** `k = 0` is excluded by the hypothesis `0 < k`. For `k = 1`,
  `Real.log 1 = 0` would make the right-hand side `0` and the statement false
  (any `r` distinct singletons already form a sunflower, but `|W| > 0` is too weak
  to extract `r` of them). To fix this the factor is written `max 1 (Real.log k)`,
  which equals `Real.log k` for all `k ≥ 3` and keeps the bound faithful in the
  regime that matters. `Real.log (k + 1)` or `Real.log k + 1` would be equally
  defensible alternatives.

- **"Contains a sunflower".** `∃ 𝒮 ⊆ W, IsSunflowerWithPetals r 𝒮`.

- **Distinctness of members.** Not stated separately; it is automatic for
  `Finset (Finset α)` and for the subfamily `𝒮`.

## Uncertainties

- I do not believe current Mathlib contains the sunflower lemma (classical or
  improved) or a named `Sunflower` predicate, so `IsSunflower` /
  `IsSunflowerWithPetals` are defined here. If such a predicate does exist (e.g. in
  `Mathlib.Combinatorics.SetFamily`), these definitions duplicate it; the intended
  identifier could not be verified without a compiler.

- Coercion insertion in `(C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k` relies on
  Mathlib's arithmetic elaborator; explicit casts were added to reduce risk, but
  this was not machine-checked.

- Binding `∀ {α : Type*} [DecidableEq α]` beneath `∃ C` inside a single theorem
  statement is expected to elaborate, but was not compiler-verified.

- `Real.log`, `Finset.card`, and the `∃ 𝒮 ⊆ W, _` binder-predicate notation are
  used from memory of Mathlib naming.
