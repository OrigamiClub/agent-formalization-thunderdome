# Agent 100 — improved sunflower lemma, statement only

## Form chosen

One `theorem improved_sunflower_lemma := by sorry` plus one auxiliary `def IsSunflower`.

The constant `C` is existentially quantified at the very outside, *before* the ambient type
`α` is introduced, so it is genuinely absolute (independent of `α`, `k`, `r`, `W`).

## Encoding decisions

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; a family is
  `W : Finset (Finset α)`; members are `Finset α`. This gives finiteness for free,
  makes `∩`, `⊆`, `card` all computable/`Finset`-native, and lets "contains a sunflower"
  be `∃ P, P ⊆ W ∧ ...` with `P : Finset (Finset α)`.
- **`α` universally quantified inside the theorem** (`∀ {α : Type*} [DecidableEq α] ...`)
  so that a single `C` works over every ambient type.
- **Sunflower definition.** Explicit core. `IsSunflower r P core` bundles three clauses:
  `P.card = r`; `core ⊆ S` for every `S ∈ P`; and `S ∩ T = core` for every pair of distinct
  `S, T ∈ P`. The pairwise-intersection clause is the mathematical heart; the `core ⊆ S`
  clause is added so the predicate is a true sunflower even in degenerate cases
  (`r = 1`, where the pairwise clause is vacuous). Pairwise-disjointness of petals and the
  "in ≥2 ⟹ in all" property are consequences, not separately stated.
- **Petals nonempty:** not required. Core may be empty (a "sunflower-free" family in the
  usual sense is one with no *disjoint* petals, i.e. empty core; the lemma statement does
  not restrict the core).
- **Distinctness of members:** free — `P` is a `Finset`, and `P.card = r` gives `r` distinct
  sets.
- **`r` petals:** `r ≥ 1` (`1 ≤ r`). The classical convention counts `r = 1` and `r = 2` as
  (degenerate) sunflowers; the interesting content is `r ≥ 3`.
- **Cardinality:** `Finset.card` throughout.
- **Logarithm:** `Real.log` (natural log). Any other base only rescales the absolute
  constant `C`, so the choice is immaterial to the statement's content.
- **`k = 0, 1` handling.** Guarded by hypothesis `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0`, so
  `(C·r·log k)^k` is `≤ 0` (or `= 1` when `k = 0`), which would make the cardinality
  hypothesis trivially satisfiable and the conclusion false (e.g. `k = 1`, `W` a single
  singleton, `r = 2`). The informal "for all positive integers `k`" is recovered by treating
  `k = 1` as a separate triviality. Using `2 ≤ k` keeps the formal statement true and matches
  standard write-ups.
- **Bound as strict `<`.** `(C * r * Real.log k) ^ k < W.card`, matching
  `|W| > (C r log k)^k`.
- **`C` supplied how:** existentially quantified inside the theorem, together with `0 < C`.

## Uncertainties

- I do **not** believe current Mathlib has a sunflower / Δ-system predicate or the sunflower
  lemma, so `IsSunflower` is defined here from scratch. If a `Finset.Sunflower` /
  `IsSunflower` does exist upstream, this local definition would shadow/collide and should be
  replaced by the library one.
- `import Mathlib` (the whole library) is used for simplicity; the only real dependency is
  `Real.log` and `Finset` API.
- Coercions `(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)` are written explicitly; exact elaboration
  (e.g. whether `Real.log (k : ℝ)` needs the annotation) is my best guess without a compiler.
- Placing an instance binder `[DecidableEq α]` after explicit binders inside a `∀` in the
  theorem type is expected to elaborate, but I could not verify it.
