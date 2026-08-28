# Agent 056 — improved sunflower lemma, statement only

## Form chosen

A single existential theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ Y P, P ⊆ W ∧ IsSunflower r Y P
```

with an auxiliary predicate `IsSunflower r Y P`.

## Encoding decisions and rationale

- **Set representation.** Sets are `Finset α` over an arbitrary ambient type `α`
  (with `[DecidableEq α]`, needed for `Finset` intersection). The family `W` is a
  `Finset (Finset α)`. This makes members automatically distinct, so no extra
  distinctness hypothesis is needed, and the family size is just `W.card : ℕ`.
- **`IsSunflower`.** Defined explicitly with a core `Y`:
  `P.card = r` (fixes the number of petals; combined with `Finset` distinctness this
  is the "`r` distinct sets" condition), `∀ S ∈ P, Y ⊆ S`, and
  `∀ S T ∈ P, S ≠ T → S ∩ T = Y`. The last clause is the standard Rao-style
  definition ("all pairwise intersections coincide"); for `r ≥ 2` it already forces
  `Y = ⋂ P` and `Y ⊆ S`, but the explicit `Y ⊆ S` clause is kept so the predicate is
  still meaningful in the degenerate `r ≤ 1` cases and matches the phrasing "there is
  a core set `Y` with …".
- **Petals nonempty.** Not imposed. In the `k`-uniform regime with distinct members
  and common pairwise intersection `Y`, we have `|Y| < k`, so every petal `S \ Y` is
  automatically nonempty.
- **Logarithm.** `Real.log` (natural log). The base of the log only affects the
  absolute constant `C`, so any fixed base gives an equivalent statement; natural log
  is the most standard Mathlib choice.
- **`k = 1` / `k = 0`.** The displayed bound `(C r log k)^k` is genuinely false at
  `k = 1` (`Real.log 1 = 0` gives RHS bound `0`, but the true sunflower function is
  `f(1,r) = r`), and `log 0` is not meaningful. So the hypothesis is `2 ≤ k`, which
  also subsumes positivity of `k`. This matches how the bound is stated in the
  literature (implicitly `k ≥ 2`).
- **`r`.** Kept as `1 ≤ r` ("positive integers r"). The `r = 1` case is a harmless
  degeneracy (any single set is a 1-petal sunflower).
- **Constant `C`.** Existentially quantified at the very front, *before* the
  quantifier over the ambient type `α`, `k`, `r`, and `W`, so it is a true absolute
  constant. `0 < C` recorded.
- **Cardinality.** `Finset.card` throughout (`S.card = k`, `W.card`), cast to `ℝ`
  for the comparison with the real-valued bound.
- **`W.card` comparison.** Stated as strict `<` ("`|W| > (C r log k)^k`"), with the
  real bound on the left and `(W.card : ℝ)` on the right.

## Uncertainties

- I am fairly confident Mathlib (early 2026) has **no** sunflower lemma or `Sunflower`
  predicate, so `IsSunflower` is defined here from scratch. If one exists it is likely
  under `Mathlib.Combinatorics.SetFamily` with a name like `Finset.IsSunflower` /
  `SetFamily.Sunflower`; not used, to stay self-contained.
- Identifiers assumed from Mathlib: `Real.log`, `Finset.card`, `Finset.instInter`
  (`S ∩ T` for `Finset`), natural-number-to-real coercion, `Monoid.npow` for `x ^ k`
  with real base and `ℕ` exponent. All standard.
- `import Mathlib` is used for simplicity rather than a minimal import list.
- Binder form `∀ (α : Type*) [DecidableEq α] …` nested inside `∃ C, …` introduces an
  auto-bound universe parameter for the theorem; this should elaborate fine but was
  not machine-checked (no compiler available).
