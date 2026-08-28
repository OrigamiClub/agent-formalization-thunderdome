# agent_045 — improved sunflower lemma (statement only)

## Form chosen

Two `theorem ... := by sorry` statements in `agent_045.lean`:

1. `improved_sunflower_lemma` — the family form: `∃ C > 0` such that any
   `Finset (Finset α)` of `k`-sets with `card > (C·r·log k)^k` contains a
   sunflower with `r` petals.
2. `improved_sunflower_lemma_function` — the `f(k,r) ≤ (C·r·log k)^k` form,
   stated for an arbitrary `f` satisfying the sunflower-function defining
   property (so no separate definition of `f` is needed).

Plus one auxiliary definition `IsSunflower r 𝒮`.

## Encoding decisions

- **Set representation:** `Finset α` for individual sets, `Finset (Finset α)`
  for the family `W`, with `[DecidableEq α]`. Chosen because everything is
  finite and cardinalities are `Finset.card` (no `Set.ncard`/finiteness
  side-conditions). Subfamily selection is `∃ 𝒮 ⊆ W, ...`.
- **Sunflower definition:** explicit core. `IsSunflower r 𝒮 :=
  𝒮.card = r ∧ ∃ Y, ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y`. The
  "every element in ≥2 sets is in all" / "petals pairwise disjoint" phrasing is
  an equivalent consequence for `r ≥ 2`, not restated. Distinctness of members
  is automatic (it's a `Finset`), so it is not separately hypothesised.
- **Petals:** exactly `r` (via `𝒮.card = r`), not "at least `r`". Petals `S \ Y`
  are allowed to be empty (classic statement does not require nonempty petals;
  at most one member can equal the core anyway).
- **Constant `C`:** existentially quantified *inside* the theorem, with `α`
  quantified under it, so `C` is a single absolute constant not depending on the
  ground type, `k`, or `r`. `0 < C` recorded.
- **Logarithm:** `Real.log` (natural log). Base choice only rescales `C`, so it
  is irrelevant to the statement. The bound `(C * r * Real.log k) ^ k` is a real
  number compared with the coerced `(W.card : ℝ)`; `^ k` is `Monoid.npow`.
- **Small `k`:** `k = 0` and `k = 1` give `Real.log k ≤ 0` and a degenerate/
  false bound, so they are excluded by `2 ≤ k` (then `Real.log k > 0`). `r` is
  constrained by `1 ≤ r`.
- **Cardinality of members:** `∀ S ∈ W, S.card = k` (exactly `k`).

## Uncertainties

- I do not believe current Mathlib contains the sunflower lemma or an
  `IsSunflower` / `Finset.IsSunflower` predicate, so I defined my own. If such a
  predicate does exist (plausible candidate names: `Finset.IsSunflower`,
  `Set.IsSunflower`, `SetFamily.IsSunflower`), the local definition could be
  replaced by it; the core-based formulation here should be equivalent.
- `import Mathlib` (blanket import) is used for safety rather than a minimal
  import list.
- Universe handling: `∀ {α : Type*}` appears under `∃ C : ℝ`; the statement is
  universe-polymorphic in `α`'s universe, which is intended (keeps `C` absolute).
- Not machine-checked: no Lean compiler was available. Coercion placement
  (`(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)`) is written explicitly to reduce
  elaboration ambiguity but has not been verified to elaborate.
