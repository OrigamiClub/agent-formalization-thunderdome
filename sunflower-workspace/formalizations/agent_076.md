# Agent 076 — improved sunflower lemma, statement formalization

## Form chosen

A single existential theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ A ∈ W, A.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ 𝒮 ⊆ W, 𝒮.card = r ∧ ∃ Y, IsSunflower 𝒮 Y
```

with a local definition

```
IsSunflower 𝒮 Y  :=  ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → A ∩ B = Y
```

## Encoding decisions and rationale

- **Set representation:** `Finset α` for a set, `Finset (Finset α)` for the
  family. This gives `Finset.card` directly, makes "each set has cardinality
  exactly `k`" a clean hypothesis (`∀ A ∈ W, A.card = k`), and makes the `r`
  petals automatically distinct (members of a `Finset`), so no separate
  distinctness hypothesis is required. `DecidableEq α` is assumed so that
  `A ∩ B` on `Finset` is available.

- **Ambient type quantified inside the statement:** `α` and `[DecidableEq α]`
  are under the `∀` that follows `∃ C`. This is deliberate so that `C` is one
  absolute constant that works for every ambient type, matching "there is an
  absolute constant `C`".

- **Sunflower predicate:** defined explicitly via "all pairwise intersections
  equal a fixed core `Y`". I did not rely on a Mathlib `Sunflower` predicate;
  see uncertainties. The core `Y` is existentially quantified. The disjoint,
  nonempty petals and the "in ≥2 ⇒ in all" property are consequences and are
  noted in the docstring rather than stated.

- **"Sunflower with r petals":** an `r`-element subfamily `𝒮 ⊆ W` that
  `IsSunflower`. Number of petals = `𝒮.card`.

- **Petals nonempty:** not imposed. With `r` distinct equal-cardinality members
  and a common pairwise intersection `Y`, at most one member can equal `Y`, so
  at least `r-1` petals are nonempty for free. Kept the statement minimal.

- **Logarithm:** `Real.log` (natural log). The base only rescales `C`, so it is
  irrelevant to the truth of the statement. RHS built in `ℝ`; `W.card` coerced
  to `ℝ` for the comparison. The exponent `k` stays `ℕ` (monoid power).

- **`k = 0`, `k = 1`:** excluded via `2 ≤ k`. For these the bound
  `(C r log k)^k` collapses to `0` and the statement would become false (e.g.
  `k = 1`: any positive number of singletons would have to contain an
  `r`-petal sunflower, but the true sunflower function is `f(1,r) = r`). This is
  a genuine limitation of the `(C r log k)^k` form, not just a log-domain issue,
  so a hypothesis exclusion is the honest encoding. `r ≥ 1` via `1 ≤ r`.

- **`C` placement:** existentially quantified inside the theorem (`∃ C, 0 < C ∧
  …`), rather than a named constant or a hypothesis, since the mathematical
  content is precisely "such a `C` exists".

- **Strict inequality** `(C r log k)^k < W.card` mirrors "|W| > (C r log k)^k".

## Uncertainties / things guessed

- **Mathlib sunflower API:** I am not confident Mathlib currently has a
  general sunflower / Δ-system predicate or the sunflower lemma. There is
  `Mathlib/Combinatorics/SetFamily/` material (e.g. Kruskal–Katona), and I
  recall sunflower-related work but not a stable public identifier such as
  `Finset.IsSunflower` or `SetFamily.Sunflower`. To be safe I defined
  `IsSunflower` locally. If a canonical predicate exists, this definition should
  be replaced by it (the intended meaning is the standard one).

- **Coercion sites:** wrote `(r : ℝ)`, `Real.log (k : ℝ)`, `(W.card : ℝ)`
  explicitly to avoid elaboration ambiguity; exact spots where Lean would insert
  `↑` automatically are not verified (no compiler available).

- **Term-level binder syntax** `∀ {α : Type*} [DecidableEq α] (k r : ℕ), …`
  inside the conjunction after `∃ C` is believed valid Lean 4, but not checked.

- **`import Mathlib`** used for a self-contained file; a minimal import set
  (`Mathlib.Data.Finset.Lattice`, `Mathlib.Analysis.SpecialFunctions.Log.Basic`)
  would also suffice.

- Alternative not taken: replacing `Real.log k` by `Real.log (k + 1)` to keep
  the bound well-defined and true for all `k ≥ 1`. This handles small `k`
  uniformly and is asymptotically equivalent, but deviates from the literal
  `(C r log k)^k`, so I preferred the `2 ≤ k` hypothesis.
