# Agent 064 — note on the formalization

## Form chosen

A single existential theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 0 < k → 0 < r →
  ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)),
    (∀ S ∈ W, S.card = k) →
    (C * r * max (Real.log k) 1) ^ k < (W.card : ℝ) →
    ∃ P ⊆ W, IsSunflower r P
```

with an auxiliary `def IsSunflower (r : ℕ) (P : Finset (Finset α)) : Prop`.

## Encoding decisions and why

- **Set family representation:** `W : Finset (Finset α)` over an arbitrary ambient
  type `α` with `[DecidableEq α]`. This gives finiteness for free, makes
  `Finset.card` the natural cardinality notion, and makes distinctness of the
  members of `W` automatic (no separate injectivity/`Set.InjOn` hypothesis needed).
  `Set α` + `Set.Finite` was the main alternative; rejected as heavier for a pure
  statement.
- **`k`-uniformity:** `∀ S ∈ W, S.card = k` (exact cardinality, as in the informal
  statement), not `≤ k`.
- **Sunflower predicate:** defined locally. I am not aware of an existing sunflower
  predicate in Mathlib (there are `Finset.Intersecting`, shadows, Kruskal–Katona,
  LYM, compressions, but no `Sunflower` to my knowledge). Definition used: `P` has
  `P.card = r` and there exists a core `Y : Finset α` with `S ∩ T = Y` for all
  distinct `S, T ∈ P` ("all pairwise intersections coincide" formulation). The
  petals `S \ Y` and the properties "core ⊆ each set", "pairwise-disjoint petals"
  are consequences and were deliberately left out of the definition to keep it
  minimal. The subfamily is delivered as `∃ P ⊆ W, IsSunflower r P`
  (i.e. `∃ P, P ⊆ W ∧ IsSunflower r P`).
- **Petals nonempty:** not required. For `r ≥ 2` each `Y = S_i ∩ S_j ⊊ S_i`
  automatically (equal cardinality `k` would force `S_i = S_j`), so petals are
  nonempty for free; for `r ≤ 1` the core condition is vacuous, which is standard
  and harmless.
- **Distinctness of the `r` petals:** automatic, since `P : Finset (Finset α)` and
  `P.card = r`.
- **Logarithm / small `k`:** natural logarithm `Real.log`. The literal bound
  `(C·r·log k)^k` is degenerate at `k = 1` (`Real.log 1 = 0` makes the RHS `0`,
  and the claim would then be false for `r ≥ 2`). I use `max (Real.log k) 1` as the
  factor: identical to `Real.log k` for every `k ≥ 3` (`Real.log 3 > 1`), and the
  finitely many small cases (`k ∈ {1,2}`) are absorbed by the absolute constant
  `C`. The hypothesis `0 < k` is kept to honour "positive integers `k`"
  (`Real.log 0 = 0` is junk in Mathlib but excluded anyway).
- **The constant `C`:** existentially quantified at the very front, `0 < C`,
  matching "there is an absolute constant `C`". The type `α`, and `k, r, W`, are all
  quantified *inside* the `∃ C`, so `C` cannot depend on them.
- **Casts:** `k, r : ℕ` are coerced to `ℝ`; `^ k` is the `Monoid.npow`
  `ℝ → ℕ → ℝ` power; the conclusion of the size hypothesis compares against
  `(W.card : ℝ)`.

## Uncertainties

- No Mathlib sunflower predicate is used; `IsSunflower` is my own. If Mathlib does
  contain one (e.g. under `Mathlib.Combinatorics.SetFamily.*`), it was not
  referenced here.
- `∀ (α : Type*)` appears under the `∃ C`, so Lean introduces one universe
  parameter for the theorem; `C` is absolute across all types in that (arbitrary)
  universe. Restricting to `Type` (universe 0) would be a minor variant.
- `import Mathlib` (whole library) is used for a self-contained statement file; the
  minimal import set was not pinned down.
- Exact instance-binder syntax `∀ (α : Type*) [DecidableEq α] (W : ...), ...` inside
  a `∀` is believed correct in current Mathlib/Lean 4 but not compiler-checked here.
- The `⦃ ⦄` strict-implicit binders in `IsSunflower` are a stylistic choice; plain
  `∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y` would be equivalent.
